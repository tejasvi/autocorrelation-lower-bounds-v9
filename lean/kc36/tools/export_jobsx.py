"""Export a verify_cmp.py certificate (square cuts, cut tables, compressed leaves; e.g. c30_132m) as one
Lean module per job, checked by native_decide with the EXTENDED checker (AutocorrCert/CheckerX.lean).

As tools/export_jobs.py, with these record types:
  I -> split, S -> delegated, K -> (cut table entry, resolved here), F -> Farkas,
  L -> leaf with all duals (+ square cuts), D / C -> compressed leaf (given duals + square cuts; the P, G and
  ZA duals are completed by the Lean checker itself, `completeX`, in the order `zo` of verify_cmp.Implied).
Encodings (base-32 varints, see export.py), in addition to export.py's:
  key  := ... | 8 v0 m (block v)*m             square cut
  rec  := ... | 3 (delegated) | 4 m (key num e)*m    compressed leaf
  zo   := count key*                            (ZA rows, parents first)
Duals must be dyadic (num / 2^e): D values are int/2^F, L values and cut multipliers are binary64.
"""
import sys, os, json, gzip, glob, argparse, time
from fractions import Fraction as Fr
from multiprocessing import get_context

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checker_path
checker_path.add_checker_path()
import verify_cmp as verify  # reference Spec (read-only): verify.py + square cuts + compressed leaves
from export import enc_int, scaled, SB, KIND

G = {}


def float_propagate(tree, L, U):
    L = list(L); U = list(U)
    L[0] = max(L[0], 1.0); U[0] = min(U[0], 1.0)
    for _ in range(64):
        changed = False
        for b, (lo, hi, par, c1, c2) in enumerate(tree):
            if c1 < 0:
                continue
            nl = max(L[b], L[c1] + L[c2]); nu = min(U[b], U[c1] + U[c2])
            l1 = max(L[c1], L[b] - U[c2]); u1 = min(U[c1], U[b] - L[c2])
            l2 = max(L[c2], L[b] - U[c1]); u2 = min(U[c2], U[b] - L[c1])
            new = (nl, nu, l1, u1, l2, u2)
            if new != (L[b], U[b], L[c1], U[c1], L[c2], U[c2]):
                changed = True
                L[b], U[b], L[c1], U[c1], L[c2], U[c2] = new
        if not changed:
            break
    else:
        raise RuntimeError("propagation did not converge")
    if any(L[b] > U[b] for b in range(len(tree))):
        return None
    return L, U


def float_child(tree, reg, b, s, side):
    L, U = list(reg[0]), list(reg[1])
    if side == 0:
        U[b] = s
    else:
        L[b] = s
    return float_propagate(tree, L, U)


def enc_path(path):
    if not path:
        return ""
    out = []
    enc_int(len(path), out)
    for b, s, side in path:
        enc_int(b, out); enc_int(scaled(s, SB), out); enc_int(side, out)
    return "".join(out)


def path_key(path):
    return tuple((b, str(s), side) for b, s, side in path)


def enc_y(y, out):
    d = y.denominator
    e = d.bit_length() - 1
    if (1 << e) != d:
        raise ValueError("non-dyadic dual")
    enc_int(y.numerator, out)
    enc_int(e, out)


def enc_base(key, y, out):
    enc_int(KIND[key[0]], out)
    for a in key[1:]:
        enc_int(a, out)
    enc_y(y, out)


def enc_sq(key, y, out):
    if not (isinstance(key, list) and len(key) == 3 and key[0] == "sq"):
        raise ValueError(f"bad sq key {key!r}")
    enc_int(8, out); enc_int(key[1], out); enc_int(len(key[2]), out)
    for b, v in key[2]:
        enc_int(b, out); enc_int(v, out)
    enc_y(y, out)


def enc_leaf(tag, rowkeys, idx, ys, extra, out):
    items = [(rowkeys[k], y) for k, y in zip(idx, ys) if y != 0]
    sqs = [(key, y) for key, y in extra if y != 0]
    enc_int(tag, out); enc_int(len(items) + len(sqs), out)
    for key, y in items:
        enc_base(key, y, out)
    for key, y in sqs:
        enc_sq(key, y, out)


def export_job(f):
    tree, root_reg, rowkeys = G["tree"], G["root"], G["rowkeys"]
    with gzip.open(f, "rt") as fh:
        h = json.loads(fh.readline())
        recs = [json.loads(line) for line in fh]
    path = [(int(b), Fr(s), int(side)) for b, s, side in h["path"]]
    reg = root_reg
    for b, s, side in path:
        reg = float_child(tree, reg, b, float(s), side)
        if reg is None:
            raise AssertionError(f"empty job root {f}")
    stack = [(reg, path)]
    children = []
    out = []
    cuts = {}

    def resolve(ex):
        return [(cuts[t[0]] if type(t[0]) is int else t[0], Fr(t[1])) for t in ex]
    nrec = sum(1 for r in recs if r[0] != "K")
    enc_int(nrec, out)
    nleaves = 0
    for rec in recs:
        kind = rec[0]
        if kind == "K":
            if rec[1] in cuts:
                raise AssertionError("cut id defined twice")
            cuts[rec[1]] = rec[2]
            continue
        reg, pth = stack.pop()
        if kind == "I":
            b, s = rec[1], Fr(rec[2])
            enc_int(0, out); enc_int(b, out); enc_int(scaled(s, SB), out)
            for side in (0, 1):
                c = float_child(tree, reg, b, float(s), side)
                if c is not None:
                    stack.append((c, pth + [(b, s, side)]))
        elif kind == "L":
            ex = resolve(rec[4]) if len(rec) == 5 else []
            enc_leaf(1, rowkeys, rec[2], [Fr(v) for v in rec[3]], ex, out); nleaves += 1
        elif kind == "D":
            ex = resolve(rec[5]) if len(rec) == 6 else []
            enc_leaf(4, rowkeys, rec[3], [Fr(v, 1 << rec[2]) for v in rec[4]], ex, out); nleaves += 1
        elif kind == "C":
            ex = resolve(rec[4]) if len(rec) == 5 else []
            enc_leaf(4, rowkeys, rec[2], [Fr(v) for v in rec[3]], ex, out); nleaves += 1
        elif kind == "F":
            enc_leaf(2, rowkeys, rec[1], [Fr(v) for v in rec[2]], [], out); nleaves += 1
        elif kind == "S":
            enc_int(3, out); children.append(pth)
        else:
            raise AssertionError(kind)
    if stack:
        raise AssertionError(f"{len(stack)} nodes left in {f}")
    return (path_key(path), enc_path(path), [path_key(c) for c in children],
            [enc_path(c) for c in children], "".join(out), nleaves, os.path.basename(f))


def init_worker(n, rowkeys):
    spec = verify.Spec(n)
    G["tree"] = spec.tree
    G["rowkeys"] = rowkeys
    G["root"] = float_propagate(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)


def scan_job(f):
    """Pass 1: structure only (no record strings kept)."""
    r = export_job(f)
    return r[0], r[1], r[2], r[3], r[5], f


def write_group(task):
    """Pass 2: write the module of one group of jobs (post-order, children first)."""
    gid, jobs, fn, header = task
    parts = [header]
    for (k, f, pstr, cstrs, kid_ids, nl) in jobs:
        r = export_job(f)
        if r[1] != pstr or r[3] != cstrs:
            raise AssertionError("pass 2 disagrees with pass 1")
        recs = r[4]
        lst = "[" + ", ".join(f'"{c}"' for c in cstrs) + "]"
        allc = ("⟨" + ", ".join(f"{G['pkgns']}.J{c}.covered" for c in kid_ids) + ", trivial⟩") if kid_ids else "trivial"
        parts.append(f"""
-- job {os.path.basename(f)}: {nl} leaves, {len(kid_ids)} delegated subtrees
namespace {G['pkgns']}.J{k}

def recs : String := "{recs}"

theorem chk : Autocorr.Cert.checkJobStrX {G['n']} {G['lamlit']} {G['pkgns']}.zo "{pstr}" {lst} recs = true := by
  native_decide

theorem covered : Autocorr.Cert.CoveredX {G['n']} {G['lamlit']} {G['pkgns']}.zo "{pstr}" :=
  .mk _ _ _ chk (Autocorr.Cert.AllCoveredX.mem {allc})

end {G['pkgns']}.J{k}
""")
    src = "".join(parts)
    old = open(fn).read() if os.path.exists(fn) else None
    if old != src:
        os.makedirs(os.path.dirname(fn), exist_ok=True)
        with open(fn, "w") as fh:
            fh.write(src)
        return 1
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("pkg", help="Lean namespace / directory under Autocorr, e.g. C24")
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--group-leaves", type=int, default=0,
                    help="put every delegation subtree with at most this many leaves into one module")
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
    G.update(n=n, lamlit=lamlit, pkgns=pkgns)
    t0 = time.time()
    ctx = get_context("fork")
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=init_worker, initargs=(n, rowkeys)) as pool:
            res = pool.map(scan_job, files, chunksize=16)
    else:
        init_worker(n, rowkeys)
        res = [scan_job(f) for f in files]
    print(f"pass 1: scanned {len(res)} jobs in {time.time()-t0:.1f}s", flush=True)
    res.sort(key=lambda r: (len(r[0]), r[0]))
    if res[0][0] != ():
        raise AssertionError("no root job")
    idx = {r[0]: k for k, r in enumerate(res)}
    if len(idx) != len(res):
        raise AssertionError("duplicate job roots")
    used = set()
    for r in res:
        for c in r[2]:
            if c not in idx:
                raise AssertionError("delegated path without job")
            if c in used:
                raise AssertionError("path delegated twice")
            used.add(c)
    if used != set(idx) - {()}:
        raise AssertionError("orphan jobs")
    kids = [[idx[c] for c in r[2]] for r in res]
    nleaf = [r[4] for r in res]
    # subtree leaf totals (children have larger k? not necessarily; use explicit post-order)
    order = []
    stack = [(0, False)]
    while stack:
        k, done = stack.pop()
        if done:
            order.append(k); continue
        stack.append((k, True))
        for c in kids[k]:
            stack.append((c, False))
    tot = [0] * len(res)
    for k in order:
        tot[k] = nleaf[k] + sum(tot[c] for c in kids[k])
    # groups: a job whose subtree is small (and whose parent's is not) roots a group with its whole subtree
    group = [None] * len(res)
    stack = [0]
    groots = []
    while stack:
        k = stack.pop()
        if tot[k] <= args.group_leaves:
            groots.append(k)
            sub = [k]
            i = 0
            while i < len(sub):
                for c in kids[sub[i]]:
                    sub.append(c)
                i += 1
            for j in sub:
                group[j] = k
        else:
            groots.append(k)
            group[k] = k
            stack.extend(kids[k])
    base = os.path.join(args.root, "Autocorr", args.pkg)
    os.makedirs(base, exist_ok=True)
    zo_src = (f"import AutocorrCert.DecodeX\n\n/-- ZA rows in completion order (verify_cmp.Implied.order). -/\n"
              f"def {pkgns}.zo : String := \"{''.join(zo_out)}\"\n")
    fz = os.path.join(base, "Zo.lean")
    if not os.path.exists(fz) or open(fz).read() != zo_src:
        open(fz, "w").write(zo_src)

    def modname(g):
        return f"Autocorr.{args.pkg}.G{g // 1000:03d}.G{g:06d}"

    def modfile(g):
        return os.path.join(base, f"G{g // 1000:03d}", f"G{g:06d}.lean")
    members = {}
    for k in order:                      # post-order: children before parents
        members.setdefault(group[k], []).append(k)
    tasks = []
    for g, ks in members.items():
        imps = sorted({group[c] for k in ks for c in kids[k] if group[c] != g})
        header = f"import Autocorr.{args.pkg}.Zo\n" + "".join(f"import {modname(h)}\n" for h in imps)
        header += "\nset_option maxRecDepth 100000\n"     # jobs with many delegated subtrees (anonymous-constructor depth)
        header += f"\n-- group of {len(ks)} jobs, {sum(nleaf[k] for k in ks)} leaves\n"
        jobs = [(k, res[k][5], res[k][1], res[k][3], kids[k], nleaf[k]) for k in ks]
        tasks.append((g, jobs, modfile(g), header))
    t1 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=init_worker, initargs=(n, rowkeys)) as pool:
            nw = sum(pool.imap_unordered(write_group, tasks, chunksize=1))
    else:
        nw = sum(write_group(t) for t in tasks)
    print(f"pass 2: wrote {nw} of {len(tasks)} group modules in {time.time()-t1:.1f}s", flush=True)
    a, b = lam.numerator, lam.denominator
    main = f"""import {modname(group[0])}
import Autocorr.Cert.SoundX

/-!
# The certificate `{os.path.basename(os.path.normpath(args.certdir))}` (n = {n}, lam = {a}/{b}) checked in Lean

{len(res)} jobs in {len(tasks)} modules (one `native_decide` per job, extended checker `checkJobStrX` with square
cuts and compressed leaves), composed through `Autocorr.Cert.CoveredX`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.{args.pkg}

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec {n})).isSome = true := by native_decide

theorem halfClaim : HalfClaim {n} ((({a} / {b} : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_coveredX {pkgns}.J0.covered rootOK

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
    json.dump({"n": n, "lam": str(lam), "jobs": len(res), "modules": len(tasks),
               "root_module": modname(group[0]), "leaves": sum(nleaf)},
              open(os.path.join(base, "export.json"), "w"))
    print(f"{len(res)} jobs, {len(tasks)} modules under {base}; leaves {sum(nleaf)}")


if __name__ == "__main__":
    main()
