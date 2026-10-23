"""Build generated Lean modules outside Lake, in dependency order, with bounded parallelism.

usage: build_dag.py ROOTDIR PKG [--jobs P] [--main Autocorr.PKG.Main] [--mem-gb G]

* Modules: every .lean file under ROOTDIR/Autocorr/PKG (plus the optional main module).
* Imports of modules outside the package must already be built by Lake (Autocorr.Cert.*).
* Make-like: a module is rebuilt if its .olean is missing or older than its source or than
  the .olean of any import inside the package.
* Each `lean` runs with `ulimit -v` (virtual memory cap, default 16 GB) and a wall-clock log.
"""
import os, sys, re, time, subprocess, argparse, json, resource
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait


HAVE_TIME = os.path.exists("/usr/bin/time")


def mem_avail_gb():
    with open("/proc/meminfo") as fh:
        for line in fh:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1024 ** 2
    return 0.0


def modfile(root, mod):
    return os.path.join(root, *mod.split(".")) + ".lean"


def olean(root, mod):
    return os.path.join(root, ".lake", "build", "lib", "lean", *mod.split(".")) + ".olean"


def ilean(root, mod):
    return os.path.join(root, ".lake", "build", "lib", "lean", *mod.split(".")) + ".ilean"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    ap.add_argument("pkg")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--main", default=None)
    ap.add_argument("--mem-gb", type=int, default=16)
    ap.add_argument("--main-mem-gb", type=int, default=96)
    ap.add_argument("--log", default=None)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--dynlib", action="append", default=[], help="pass --load-dynlib=PATH to lean")
    ap.add_argument("--tstack", type=int, default=0, help="lean --tstack (KB); also sets RLIMIT_STACK unlimited")
    ap.add_argument("--min-avail-gb", type=float, default=0,
                    help="start a module only while MemAvailable is above this (memory-aware scheduling)")
    ap.add_argument("--exclude", default=None,
                    help="file of modules built elsewhere: not built here; their dependents stay pending (exit 3)")
    ap.add_argument("--kill-avail-gb", type=float, default=0,
                    help="watchdog: below this MemAvailable, kill the youngest running module and requeue it")
    ap.add_argument("--lean-path", default=None, help="LEAN_PATH to use instead of `lake env` (machines without lake/git)")
    ap.add_argument("--rm-src", action="store_true",
                    help="delete the source of each generated module (not the main module) once it is built")
    args = ap.parse_args()
    root = os.path.abspath(args.root)
    lp = args.lean_path or subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, capture_output=True,
                                          text=True, check=True).stdout.strip()
    pkgdir = os.path.join(root, "Autocorr", args.pkg)
    mods = []
    for d, _, fs in os.walk(pkgdir):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(d, f), root)[:-5]
                mods.append(rel.replace(os.sep, "."))
    if args.main and args.main not in mods:
        mods.append(args.main)
    modset = set(mods)
    deps = {}
    imp_re = re.compile(r"^import\s+(\S+)", re.M)
    for m in mods:
        src = open(modfile(root, m)).read(4096 * 64)
        deps[m] = [x for x in imp_re.findall(src) if x in modset]
    # topological levels + make-like staleness
    state = {}
    order = []
    sys.setrecursionlimit(100000)

    def visit(m):
        if m in state:
            return
        state[m] = 0
        for d in deps[m]:
            visit(d)
        order.append(m)
    for m in mods:
        visit(m)
    stale = set()
    for m in order:
        o = olean(root, m)
        if (not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(modfile(root, m))
                or any(d in stale or os.path.getmtime(olean(root, d)) > os.path.getmtime(o) for d in deps[m])):
            stale.add(m)
    excl = set(open(args.exclude).read().split()) if args.exclude else set()
    todo = [m for m in order if m in stale and m not in excl]
    stale_excl = [m for m in order if m in stale and m in excl]
    print(f"{len(mods)} modules, {len(todo)} to build, jobs={args.jobs}", flush=True)
    env = dict(os.environ, LEAN_PATH=lp)
    logf = open(args.log or os.path.join(root, f"build_{args.pkg}.log"), "a")
    done = set(m for m in mods if m not in stale)
    pending_deps = {m: set(d for d in deps[m] if d not in done) for m in todo}
    if stale_excl:
        print(f"{len(stale_excl)} stale modules excluded (built elsewhere)", flush=True)
    rdeps = {}
    for m in todo:
        for d in pending_deps[m]:
            rdeps.setdefault(d, []).append(m)
    ready = [m for m in todo if not pending_deps[m]]
    t0 = time.time()
    failed = []
    memcap = args.mem_gb * 1024 * 1024 * 1024

    def build(m):
        os.makedirs(os.path.dirname(olean(root, m)), exist_ok=True)
        ts = time.time()

        cap = args.main_mem_gb * 1024 ** 3 if m == args.main else memcap

        def limit():
            hard = resource.getrlimit(resource.RLIMIT_AS)[1]
            c = cap if hard == resource.RLIM_INFINITY else min(cap, hard)     # never above an inherited cap
            resource.setrlimit(resource.RLIMIT_AS, (c, c))
            try:                                   # the OOM killer should pick a lean job, not the scheduler
                with open("/proc/self/oom_score_adj", "w") as fh:
                    fh.write("800")
            except OSError:
                pass
            if args.tstack:
                resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
        dl = [f"--load-dynlib={p}" for p in args.dynlib]
        ts_opt = [f"--tstack={args.tstack}"] if args.tstack else []
        cmd = (["/usr/bin/time", "-f", "@@TIME %e %U %M"] if HAVE_TIME else []) + [args.lean] + dl + ts_opt + \
            ["-o", olean(root, m), "-i", ilean(root, m), modfile(root, m)]
        pr = subprocess.Popen(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                              preexec_fn=limit, cwd=root, start_new_session=True)
        procs[m] = (pr, ts)
        if HAVE_TIME:
            out, _ = pr.communicate()
            rc = pr.returncode
        else:                     # no /usr/bin/time (minimal images): the same three numbers from wait4's rusage
            out = pr.stdout.read()
            _, st, ru = os.wait4(pr.pid, 0)
            rc = pr.returncode = os.waitstatus_to_exitcode(st)
            out += f"\n@@TIME {time.time() - ts:.2f} {ru.ru_utime:.2f} {ru.ru_maxrss}\n"
        procs.pop(m, None)
        return m, rc, out, time.time() - ts

    nbuilt = 0
    procs = {}
    killed = set()
    retries = {}
    last_kill = 0.0
    nkill = 0
    with ThreadPoolExecutor(args.jobs) as ex:
        running = {}
        while ready or running:
            while ready and len(running) < args.jobs:
                if args.min_avail_gb and running and mem_avail_gb() < args.min_avail_gb:
                    break
                m = ready.pop()
                running[ex.submit(build, m)] = m
                if args.min_avail_gb and mem_avail_gb() < 2 * args.min_avail_gb:
                    time.sleep(0.2)                  # rate-limit starts only when memory gets tight
            fin, _ = wait(list(running), return_when=FIRST_COMPLETED, timeout=1 if args.min_avail_gb else None)
            if (args.kill_avail_gb and len(procs) > 1 and time.time() - last_kill > 5
                    and mem_avail_gb() < args.kill_avail_gb):
                last_kill = time.time()
                young = max(procs.items(), key=lambda kv: kv[1][1])
                try:
                    os.killpg(young[1][0].pid, 9)        # explicit process group of that module's build
                    killed.add(young[0]); nkill += 1
                    print(f"watchdog: MemAvailable {mem_avail_gb():.0f} GB, killed {young[0]} (requeued)", flush=True)
                except ProcessLookupError:
                    pass
            for fu in fin:
                m = running.pop(fu)
                m, rc, out, dt = fu.result()
                oom = rc in (-9, 137) or "terminated by signal 9" in out      # SIGKILL: OOM killer or watchdog
                if m in killed or (oom and retries.get(m, 0) < 3):
                    killed.discard(m)
                    retries[m] = retries.get(m, 0) + 1
                    ready.insert(0, m)               # retried last (ready is used as a stack)
                    logf.write(json.dumps({"mod": m, "killed": True, "sec": round(dt, 2)}) + "\n")
                    continue
                nbuilt += 1
                tl = [l for l in out.splitlines() if l.startswith("@@TIME ")]
                rec = {"mod": m, "rc": rc, "sec": round(dt, 2), "out": out[-2000:]}
                if tl:
                    e, u, mx = tl[-1].split()[1:4]
                    rec.update(wall=float(e), user=float(u), maxrss_mb=round(int(mx) / 1024))
                logf.write(json.dumps(rec) + "\n")
                logf.flush()
                if rc != 0:
                    failed.append(m)
                    print(f"FAILED {m} ({dt:.1f}s): {out[-500:]}", flush=True)
                    continue
                if args.rm_src and m != args.main:
                    os.remove(modfile(root, m))
                for r2 in rdeps.get(m, []):
                    pending_deps[r2].discard(m)
                    if not pending_deps[r2]:
                        ready.append(r2)
                if nbuilt % 100 == 0:
                    print(f"  {nbuilt}/{len(todo)} built, {time.time()-t0:.0f}s", flush=True)
    print(f"built {nbuilt} modules in {time.time()-t0:.1f}s; failed {len(failed)}; watchdog kills {nkill}", flush=True)
    blocked = [m for m in todo if pending_deps[m]]
    if blocked:
        print(f"{len(blocked)} modules wait for excluded or failed modules", flush=True)
    sys.exit(1 if failed else (3 if blocked else 0))


if __name__ == "__main__":
    main()
