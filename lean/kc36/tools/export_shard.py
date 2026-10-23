"""Sharded export of a (filled) verify_cmp-format certificate for the extended native checker (CheckerX).

Same modules as tools/export_jobsx.py (imported; its encoding, pass 1 and checker calls are reused unchanged), but
jobs and modules are named by job file id instead of by a global index, so that disjoint sets of jobs can be
exported and built on different machines and composed afterwards:

    job      <id>.jsonl.gz            ->  namespace Autocorr.PKG.J<id>   (chk, covered as in export_jobsx)
    group    rooted at job <gid>      ->  module    Autocorr.PKG.G<gid[:2]>.G<gid>

usage:
  export_shard.py CERTDIR PKG [--workers W] [--group-leaves G] [--external EXT.json] [--main] [--root ROOT]
  CERTDIR   meta.json + jobs/*.jsonl.gz: the jobs of this shard.  A build shard holds complete delegation subtrees
            (every delegated path of a job is the root path of another job of the shard); the assembly shard holds
            the jobs near the root and lists the roots of the build shards' subtrees in EXT.json.
  EXT.json  {"<enc_path of a delegated root>": "<job id>", ...}: delegated subtrees exported elsewhere.  The
            group of an external subtree root is the subtree root itself (every subtree root roots its group), so
            its module name is known: Autocorr.PKG.G<id[:2]>.G<id>.
  --main    write Main.lean (requires the job with the empty root path); only for the assembly shard.
  --single-group  put all jobs of the shard into one module (one local root); for a small assembly shard, so that
            the whole import closure is loaded once instead of once per level of the assembly tree.
Nothing here is trusted: the theorem `covered` of each job is checked by native_decide over its own records and
composed with the children's `covered` exactly as in export_jobsx.
"""
import sys, os, json, glob, argparse, time, hashlib
from fractions import Fraction as Fr
from multiprocessing import get_context

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import export_jobsx as X        # noqa: E402  (pass 1 scan, record encoding, init_worker, G)
from export_jobsx import verify, enc_int, KIND   # noqa: E402


def jid(f):
    b = os.path.basename(f)
    assert b.endswith(".jsonl.gz")
    return b[:-len(".jsonl.gz")]


def gname(pkg, gid):
    return f"Autocorr.{pkg}.G{gid[:2]}.G{gid}"


def write_group_id(task):
    """Pass 2: the module of one group (post-order, children first); names by job id.  With --skip-unchanged, a group
    whose source sha256 equals the sidecar <module>.lean.sha256 of an earlier export AND whose .olean exists is not
    written (it is already built; build_dag then treats it as built outside the package sources)."""
    gid, jobs, fn, header, ofn = task
    pk = X.G["pkgns"]
    parts = [header]
    for (k, f, pstr, cstrs, kid_ids, nl) in jobs:
        r = X.export_job(f)
        if r[1] != pstr or r[3] != cstrs:
            raise AssertionError("pass 2 disagrees with pass 1")
        recs = r[4]
        lst = "[" + ", ".join(f'"{c}"' for c in cstrs) + "]"
        allc = ("⟨" + ", ".join(f"{pk}.J{c}.covered" for c in kid_ids) + ", trivial⟩") if kid_ids else "trivial"
        parts.append(f"""
-- job {os.path.basename(f)}: {nl} leaves, {len(kid_ids)} delegated subtrees
namespace {pk}.J{k}

def recs : String := "{recs}"

theorem chk : Autocorr.Cert.checkJobStrX {X.G['n']} {X.G['lamlit']} {pk}.zo "{pstr}" {lst} recs = true := by
  native_decide

theorem covered : Autocorr.Cert.CoveredX {X.G['n']} {X.G['lamlit']} {pk}.zo "{pstr}" :=
  .mk _ _ _ chk (Autocorr.Cert.AllCoveredX.mem {allc})

end {pk}.J{k}
""")
    src = "".join(parts)
    h = hashlib.sha256(src.encode()).hexdigest()
    side = fn + ".sha256"
    if ofn and os.path.exists(ofn) and os.path.exists(side) and open(side).read() == h:
        if os.path.exists(fn) and open(fn).read() != src:
            os.remove(fn)
        return 0
    old = open(fn).read() if os.path.exists(fn) else None
    if old != src:
        os.makedirs(os.path.dirname(fn), exist_ok=True)
        with open(fn, "w") as fh:
            fh.write(src)
        with open(side, "w") as fh:
            fh.write(h)
        return 1
    if not os.path.exists(side):
        with open(side, "w") as fh:
            fh.write(h)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("pkg")
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--group-leaves", type=int, default=3000)
    ap.add_argument("--external", default=None)
    ap.add_argument("--main", action="store_true")
    ap.add_argument("--skip-unchanged", action="store_true",
                    help="do not rewrite groups whose source hash matches an earlier export and whose .olean exists")
    ap.add_argument("--single-group", action="store_true",
                    help="all jobs in one module (requires a single local root; meant for a small assembly shard)")
    args = ap.parse_args()
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [spec.validate_key(tuple(k)) for k in meta["rowkeys"]]
    imp = verify.Implied(spec, rowkeys)
    zo_out = []
    enc_int(len(imp.order), zo_out)
    for r in imp.order:
        key = rowkeys[r]
        enc_int(KIND[key[0]], zo_out)
        for a in key[1:]:
            enc_int(a, zo_out)
    files = sorted(glob.glob(os.path.join(args.certdir, "jobs", "*.jsonl.gz")))
    lamlit = f"({lam.numerator}/{lam.denominator} : Rat)"
    pkgns = f"Autocorr.{args.pkg}"
    X.G.update(n=n, lamlit=lamlit, pkgns=pkgns)
    ext = json.load(open(args.external)) if args.external else {}
    t0 = time.time()
    ctx = get_context("fork")
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=X.init_worker, initargs=(n, rowkeys)) as pool:
            res = pool.map(X.scan_job, files, chunksize=16)
    else:
        X.init_worker(n, rowkeys)
        res = [X.scan_job(f) for f in files]
    print(f"pass 1: scanned {len(res)} jobs in {time.time()-t0:.1f}s", flush=True)
    # res entries: (path_key, enc_path, children keys, children enc paths, nleaves, file)
    ids = [jid(r[5]) for r in res]
    if len(set(ids)) != len(ids):
        raise AssertionError("duplicate job ids")
    bykey = {r[0]: i for i, r in enumerate(res)}
    if len(bykey) != len(res):
        raise AssertionError("duplicate job roots")
    used = set()
    kid_ids = []          # per job: child job ids (record order)
    kid_local = []        # per job: child indices that are local (for the post-order / groups)
    ext_used = set()
    for r in res:
        ki, kl = [], []
        for ck, cenc in zip(r[2], r[3]):
            if ck in used:
                raise AssertionError("path delegated twice")
            used.add(ck)
            if ck in bykey:
                ki.append(ids[bykey[ck]]); kl.append(bykey[ck])
            elif cenc in ext:
                ki.append(ext[cenc]); ext_used.add(cenc)
            else:
                raise AssertionError(f"delegated path without job (job {ids[bykey[r[0]]]})")
        kid_ids.append(ki); kid_local.append(kl)
    if set(ext) - ext_used:
        raise AssertionError("external subtree roots not delegated by any job of this shard")
    roots = [i for i, r in enumerate(res) if r[0] not in used]
    if args.main:
        if () not in bykey or roots != [bykey[()]]:
            raise AssertionError("--main needs exactly one local root, the job with the empty path")
    nleaf = [r[4] for r in res]
    order = []
    for r0 in roots:
        stack = [(r0, False)]
        while stack:
            k, done = stack.pop()
            if done:
                order.append(k); continue
            stack.append((k, True))
            for c in kid_local[k]:
                stack.append((c, False))
    if len(order) != len(res):
        raise AssertionError("jobs not reachable from the shard roots")
    tot = [0] * len(res)
    for k in order:
        tot[k] = nleaf[k] + sum(tot[c] for c in kid_local[k]) + (10 ** 18 if len(kid_local[k]) != len(kid_ids[k]) else 0)
    group = [None] * len(res)
    stack = [] if args.single_group else list(roots)
    if args.single_group:
        if len(roots) != 1:
            raise AssertionError("--single-group needs exactly one local root")
        group = [roots[0]] * len(res)
    while stack:                      # every shard root roots its own group (external references rely on this)
        k = stack.pop()
        if tot[k] <= args.group_leaves:
            sub = [k]; i = 0
            while i < len(sub):
                sub.extend(kid_local[sub[i]]); i += 1
            for j in sub:
                group[j] = k
        else:
            group[k] = k
            stack.extend(kid_local[k])
    base = os.path.join(args.root, "Autocorr", args.pkg)
    os.makedirs(base, exist_ok=True)
    zo_src = (f"import AutocorrCert.DecodeX\n\n/-- ZA rows in completion order (verify_cmp.Implied.order). -/\n"
              f"def {pkgns}.zo : String := \"{''.join(zo_out)}\"\n")
    fz = os.path.join(base, "Zo.lean")
    if not os.path.exists(fz) or open(fz).read() != zo_src:
        open(fz, "w").write(zo_src)

    def modfile(g):
        return os.path.join(base, f"G{ids[g][:2]}", f"G{ids[g]}.lean")
    members = {}
    for k in order:
        members.setdefault(group[k], []).append(k)
    ext_mod = {ext[c]: gname(args.pkg, ext[c]) for c in ext_used}
    tasks = []
    for g, ks in members.items():
        imps = set()
        for k in ks:
            for c in kid_local[k]:
                if group[c] != g:
                    imps.add(gname(args.pkg, ids[group[c]]))
            for cid in kid_ids[k]:
                if cid in ext_mod:
                    imps.add(ext_mod[cid])
        header = f"import Autocorr.{args.pkg}.Zo\n" + "".join(f"import {m}\n" for m in sorted(imps))
        header += "\nset_option maxRecDepth 100000\n"
        header += f"\n-- group of {len(ks)} jobs, {sum(nleaf[k] for k in ks)} leaves\n"
        jobs = [(ids[k], res[k][5], res[k][1], res[k][3], kid_ids[k], nleaf[k]) for k in ks]
        ofn = (os.path.join(args.root, ".lake", "build", "lib", "lean", "Autocorr", args.pkg, f"G{ids[g][:2]}",
                            f"G{ids[g]}.olean") if args.skip_unchanged else None)
        tasks.append((ids[g], jobs, modfile(g), header, ofn))
    t1 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=X.init_worker, initargs=(n, rowkeys)) as pool:
            nw = sum(pool.imap_unordered(write_group_id, tasks, chunksize=1))
    else:
        nw = sum(write_group_id(t) for t in tasks)
    print(f"pass 2: wrote {nw} of {len(tasks)} group modules in {time.time()-t1:.1f}s", flush=True)
    info = {"n": n, "lam": str(lam), "jobs": len(res), "modules": len(tasks), "leaves": sum(nleaf),
            "roots": [ids[r] for r in roots], "root_modules": [gname(args.pkg, ids[r]) for r in roots],
            "external": sorted(ext_used and [ext[c] for c in ext_used])}
    if args.main:
        a, b = lam.numerator, lam.denominator
        root = roots[0]
        main = f"""import {gname(args.pkg, ids[root])}
import Autocorr.Cert.SoundX

/-!
# The certificate `{os.path.basename(os.path.normpath(args.certdir))}` (n = {n}, lam = {a}/{b}) checked in Lean

Composed from sharded modules (tools/export_shard.py): one `native_decide` per job (extended checker
`checkJobStrX`), composed through `Autocorr.Cert.CoveredX`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.{args.pkg}

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec {n})).isSome = true := by native_decide

theorem halfClaim : HalfClaim {n} ((({a} / {b} : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_coveredX {pkgns}.J{ids[root]}.covered rootOK

lemma ofReal_lam : ENNReal.ofReal ((({a} / {b} : ℚ)) : ℝ) = ({a} / {b} : ℝ≥0∞) := by
  rw [show ((({a} / {b} : ℚ)) : ℝ) = ({a} : ℝ) / {b} by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ {a}/{b}`: for every measurable `f : ℝ → [0, ∞]`,
`{a}/{b} · (∫_{{-1/4}}^{{1/4}} f)² ≤ sup_{{t ∈ [-1/2, 1/2]}} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ({a} / {b} : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end Autocorr.{args.pkg}
"""
        with open(os.path.join(base, "Main.lean"), "w") as fh:
            fh.write(main)
    json.dump(info, open(os.path.join(base, "export_shard.json"), "w"))
    print(f"{len(res)} jobs, {len(tasks)} modules under {base}; leaves {sum(nleaf)}; roots {len(roots)}")


if __name__ == "__main__":
    main()
