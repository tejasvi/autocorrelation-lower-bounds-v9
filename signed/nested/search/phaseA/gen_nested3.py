# Production driver for nested certificates (phases): A = root of every T1 arc (E arcs, closed roots, or a root stub with
# its hard intervals cut into tasks); B = one Pool task per hard piece (adaptive bisection, children by gen_nested2.search);
# C = join stubs + task entries into N arcs.  usage:
#   gen_nested3.py A CFG ARCLIST.json PROCS OUT_A.jsonl          (ARCLIST: list of fine indices k or "s0:s1" strings)
#   gen_nested3.py B CFG TASKS.jsonl PROCS OUT_B.jsonl            (TASKS: lines {"k","tile","q0","q1","ts","ms"} from phase A)
#   gen_nested3.py C OUT_A.jsonl [OUT_B.jsonl ...] OUT_ARCS.jsonl
# env: TAU (rational), MAXNEST (default 2), D_TASK (max arc diameter of a task piece, default 0.01), NDIR, NT_EMIT, ...
import sys, os, json, time, hashlib
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import gen_nested2 as GN
import check_nested as CN
from multiprocessing import Pool

def module_shas():
    out = {}
    for name in ("gen_nested2", "check_nested", "nest3", "nest2", "nest_proto", "gen_two_level", "hslp"):
        m = sys.modules.get(name)
        if m is not None and getattr(m, "__file__", None):
            out[name] = hashlib.sha256(open(m.__file__, "rb").read()).hexdigest()[:16]
    out["gen_nested3"] = hashlib.sha256(open(__file__, "rb").read()).hexdigest()[:16]
    return out

def setup(cfg):
    tau = Fr(os.environ.get("TAU", cfg["tau"]))
    c, a_, b_ = (Fr(x) for x in cfg["T1"])
    tiles = {}
    for nm, t in cfg["tiles"].items():
        tiles[nm + "up"] = (Fr(t[0]), Fr(t[1]), Fr(t[2]), Fr(t[3])); tiles[nm + "dn"] = (Fr(t[0]), -Fr(t[1]), Fr(t[2]), Fr(t[3]))
    return {"nH": 4096, "nE": 512, "maxnest": int(os.environ.get("MAXNEST", "2")),
            "cn": {"tau": tau, "T1": (c, Fr(0), a_, b_), "tiles": tiles, "iv_eps": GN.IV_EPS}}

def arc_bounds(k):
    if isinstance(k, str):
        a, b = k.split(":"); return Fr(a), Fr(b)
    return Fr(k, 4096), Fr(k + 1, 4096)

def make_ctx(k):
    s0, s1 = arc_bounds(k); sc = (s0 + s1)/2
    ctx = GN.Arc(); ctx.s0, ctx.s1, ctx.sc = s0, s1, sc
    ctx.zc = CN.ell_ball(GN.G["cn"]["T1"], sc, sc); ctx.Sc = CN.S(ctx.zc); ctx.pcs = []; ctx.kc = {}
    up = float(ctx.zc.imag.mid()) >= 0
    ctx.tiles = {nm: t for nm, t in GN.G["cn"]["tiles"].items() if nm.endswith("up" if up else "dn")}; ctx.last = {}
    return ctx

def phase_A(k):
    GN.STATS.clear(); t0 = time.time()
    s0, s1 = arc_bounds(k); tau = GN.G["cn"]["tau"]
    T1 = GN.G2.Ell((GN.G["cn"]["T1"][0], Fr(0)), GN.G["cn"]["T1"][2], GN.G["cn"]["T1"][3])
    rE = GN.G2.solve_E((T1, s0, s1, tau))
    if rE is not None: return {"k": k, "result": rE, "stats": {"E": 1}, "dt": time.time() - t0}
    ctx = make_ctx(k)
    try:
        root = GN.search(ctx, [], 0, GN.G["maxnest"], {}, tau, stub_root=True)
    except RuntimeError:
        root = None; GN.STATS['budget'] = 1
    if root is None: return {"k": k, "result": {"fail": True, "s0": str(s0)}, "stats": dict(GN.STATS), "dt": time.time() - t0}
    if root.get("stub"):
        dtask = float(os.environ.get("D_TASK", "0.01")); tile = ctx.tiles[root["tile"]]; tasks = []
        for a, b in root["hard"]:
            st = [(Fr(a), Fr(b))]
            while st:
                x, y = st.pop()
                if GN.arc_diam(tile, x, y) > dtask: m = (x + y)/2; st += [(x, m), (m, y)]
                else: tasks.append([str(x), str(y)])
        tasks.sort(key=lambda t: Fr(t[0]))
        return {"k": k, "stub": root, "tasks": tasks, "stats": dict(GN.STATS), "dt": time.time() - t0}
    sc = (s0 + s1)/2
    return {"k": k, "result": {"type": "N", "s0": str(s0), "s1": str(s1), "sc": str(sc), "pcs": [], "Rs": [], "tree": root},
            "stats": dict(GN.STATS), "dt": time.time() - t0}

def phase_B(task):
    GN.STATS.clear(); t0 = time.time()
    k = task["k"]; ctx = make_ctx(k); tau = GN.G["cn"]["tau"]
    tile = ctx.tiles[task["tile"]]; ts = tuple(Fr(t) for t in task["ts"]); ms = tuple(Fr(m) for m in task["ms"])
    entries = []; stack = [(Fr(task["q0"]), Fr(task["q1"]))]; ok = True
    try:
        while stack:
            x, y = stack.pop()
            tb = ("iv", tile, x, y, ts, ms)
            dd = GN.arc_diam(tile, x, y); child = None
            if dd <= GN.DMAX:
                GN.bump('sub')
                child = GN.search(ctx, [tb], 1, GN.G["maxnest"], {}, tau, d_self=dd)
            if child is not None:
                entries.append({"hard": [str(x), str(y)], "kind": "iv", "child": child}); continue
            if y - x < Fr(1, 2**22): ok = False; break
            m = (x + y)/2; stack += [(x, m), (m, y)]
    except RuntimeError:
        ok = False; GN.bump('budget')
    return {"k": k, "q0": task["q0"], "q1": task["q1"], "ok": ok, "entries": entries if ok else None,
            "stats": dict(GN.STATS), "dt": time.time() - t0}

def init(g):
    GN.init(g)

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "C":
        outs = sys.argv[2:-1]; dst = sys.argv[-1]
        stubs = {}; done = []; tasks_need = {}; got = {}
        for fn in outs:
            for l in open(fn):
                r = json.loads(l)
                key = json.dumps(r["k"])
                if "stub" in r:
                    stubs[key] = r; tasks_need[key] = [tuple(t) for t in r["tasks"]]
                elif "entries" in r:
                    if r["ok"]: got.setdefault(key, {})[(r["q0"], r["q1"])] = r["entries"]
                elif "result" in r and "fail" not in r["result"]:
                    done.append(r["result"])
        nj = 0; missing = []
        for key, st in stubs.items():
            have = got.get(key, {})
            if not all(t in have for t in tasks_need[key]):
                missing.append(key); continue
            leaf = dict(st["stub"]); leaf.pop("stub"); w1 = leaf.pop("w1_arcs"); leaf.pop("hard")
            leaf["tile_arcs"] = w1 + [e for t in tasks_need[key] for e in have[t]]
            k = json.loads(key); s0, s1 = arc_bounds(k)
            done.append({"type": "N", "s0": str(s0), "s1": str(s1), "sc": str((s0 + s1)/2), "pcs": [], "Rs": [], "tree": leaf}); nj += 1
        with open(dst, "w") as fh:
            for r in done: fh.write(json.dumps({"k": None, "result": r}) + "\n")
        print(f"joined {nj} stub arcs; {len(done)} arcs written; {len(missing)} stub arcs missing tasks: {missing[:10]}")
        sys.exit(0)
    cfg = json.load(open(sys.argv[2])); g = setup(cfg); procs = int(sys.argv[4]); out = sys.argv[5]
    t0 = time.time()
    print("module shas", json.dumps(module_shas()), flush=True)
    if mode == "A":
        items = json.load(open(sys.argv[3])); fn = phase_A
    else:
        items = [json.loads(l) for l in open(sys.argv[3])]; fn = phase_B
    done = set()
    if os.path.exists(out):
        for l in open(out):
            r = json.loads(l); done.add(json.dumps([r["k"], r.get("q0"), r.get("q1")]))
    items = [it for it in items if json.dumps([it if mode == "A" else it["k"], None if mode == "A" else it["q0"], None if mode == "A" else it["q1"]]) not in done]
    J = open(out, "a")
    with Pool(procs, initializer=init, initargs=(g,)) as pool:
        open(out + ".pid", "w").write(f"{os.getpid()}\n")
        for i, r in enumerate(pool.imap_unordered(fn, items, chunksize=1)):
            J.write(json.dumps(r) + "\n"); J.flush()
            if (i + 1) % max(1, len(items)//50) == 0 or ("result" in r and "fail" in r["result"]) or ("ok" in r and not r["ok"]):
                print(f"[{time.time()-t0:7.1f}s] {i+1}/{len(items)} last k={r['k']} {'FAIL' if ('ok' in r and not r['ok']) or ('result' in r and 'fail' in r['result']) else 'ok'} {r['stats']}", flush=True)
    print(f"[{time.time()-t0:7.1f}s] DONE {len(items)} items", flush=True)
