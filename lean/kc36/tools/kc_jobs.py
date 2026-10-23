"""Milestone M4: export a verify.py certificate as Lean modules checked by the KERNEL (AutocorrK).

Also reads format-2 certificates with square cuts (verify_cmp.py semantics; e.g. the filled tree-only certificates
written by tools/tree/verify_tree_dump.py): K records (cut table), L records with a 5th field of square cuts
([[key or cut id, y], ...]); every key is validated by verify_cmp.Spec.sq_row.  A cut becomes a KC cut record
(kc_ref.kc_cut_duals: multiplier floored to 2^-94); every leaf is re-checked exactly (kc_ref) with its cuts.  The records
C, D, F, U, T and I records with an empty child are not supported (the export stops with an error).

Per job (parallel):
  * replay the job's DFS with exact propagation (binary64 is exact here: all bounds are multiples of 2^-30
    in [0, 1] and every update adds or subtracts two of them), recording for each split the number of sweeps
    that changed something (k0, k1);
  * leaf duals -> KC duals (window rows rescaled, rounded to 2^-64) and an EXACT re-check (tools/kc_ref.py);
  * records in the AutocorrK.runK format (2-bit tags: 0 split, 1 leaf, 2 delegated), cut into segments of at
    most --seg-leaves leaves; the interface of two segments is the explicit DFS stack (packed boxes).
Modules (core Lean only; subtrees of at most --group-leaves leaves per group; per group a check module C...
importing only Params and an assembly module G... importing the checks and the children's G modules), for every
job k (children first) and segment i:
    def jb<k> : Nat × Nat := (nat_b64% "<L>", nat_b64% "<U>")           -- job root box
    def jd<k>_<i> : Nat := nat_b64% "<records>"
    theorem jc<k>_<i> : segCheck P a b nrec jd<k>_<i> SIN SOUT = true := by decide +kernel
    theorem jfull<k> : StkK P a b [jb<k>] := .seg _ _ jc<k>_1 (.cons jfull<c> ... (.seg _ _ jc<k>_2 ...))
Nothing computed here is trusted: boxes are recomputed by the kernel (propagation), delegated boxes are
compared with the children's root boxes, and the root box with the kernel propagation of [0, 1]^nB.
"""
import sys, os, json, gzip, glob, argparse, time, base64
from fractions import Fraction as Fr
from multiprocessing import get_context

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checker_path
checker_path.add_checker_path()
import verify
import verify_cmp
import kc_ref
import kc_export as KE

G = {}
SB = 30


def b64(n):
    return base64.b64encode(n.to_bytes((n.bit_length() + 7) // 8, "little")).decode() if n else ""


def pack(parts):
    """Little-endian concatenation of (value, width) fields, by halving (fast for long lists)."""
    def rec(lo, hi):
        if hi - lo == 1:
            return parts[lo]
        mid = (lo + hi) // 2
        a, wa = rec(lo, mid)
        b, wb = rec(mid, hi)
        return a | (b << wa), wa + wb
    return rec(0, len(parts))[0] if parts else 0


def fprop(tree, L, U):
    """Float propagation (verify.Spec.propagate semantics) with the number of sweeps that changed something."""
    L = list(L); U = list(U)
    L[0] = max(L[0], 1.0); U[0] = min(U[0], 1.0)
    k = 0
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
        k += 1
    else:
        raise RuntimeError("no convergence")
    if any(L[b] > U[b] for b in range(len(tree))):
        return None, k
    return (L, U), k


def fchild(tree, reg, b, s, side):
    L, U = list(reg[0]), list(reg[1])
    if side == 0:
        U[b] = s
    else:
        L[b] = s
    return fprop(tree, L, U)


def pk_box(reg):
    lp = up = 0
    for b, (x, y) in enumerate(zip(reg[0], reg[1])):
        xi = x * (1 << SB); yi = y * (1 << SB)
        assert xi == int(xi) and yi == int(yi) and 0 <= xi <= yi <= (1 << 30)
        lp |= int(xi) << (32 * b); up |= int(yi) << (32 * b)
    return lp, up


def path_key(path):
    return tuple((b, str(s), side) for b, s, side in path)


YMAX = int(os.environ.get("KC_YMAX", (1 << 72) - 1))   # KC_YMAX: test hook (forces splitting)


def split_big(duals):
    """A dual of magnitude >= 2^72 (the record field width) is written as several entries of the same row with
    the same sign: every entry is a valid inequality times a multiplier of the admissible sign, and the bound is
    linear in the multipliers, so the value is unchanged (and it is re-checked exactly on the split list)."""
    out = []
    for key, Y in duals:
        sg = 1 if Y > 0 else -1
        m = abs(Y)
        while m > YMAX:
            out.append((key, sg * YMAX)); m -= YMAX
        out.append((key, sg * m))
    return out


def kc_job(f, seg_leaves):
    """Returns (root path key, root box, segments, nleaves, file); a segment is
    (nrec, data, delegated path keys, boxes of the stack at its end (head first))."""
    tree, root, ks, rindex, lam = G["tree"], G["root"], G["ks"], G["rindex"], G["lam"]
    rowkeys = G["rowkeys"]
    vspec = G["vspec"]
    with gzip.open(f, "rt") as fh:
        h = json.loads(fh.readline())
        recs = [json.loads(line) for line in fh]
    path = [(int(b), Fr(s), int(side)) for b, s, side in h["path"]]
    reg = root
    for b, s, side in path:
        reg, _ = fchild(tree, reg, b, float(s), side)
        if reg is None:
            raise AssertionError(f"empty job root {f}")
    stack = [(reg, path)]
    segs = []
    parts, nrec, nl_seg, dels = [], 0, 0, []
    nleaves = 0
    cuts = {}
    last = max((i for i, r in enumerate(recs) if r[0] != "K"), default=-1)

    def resolve(ex):
        out = []
        for t in ex:
            key = t[0]
            if type(key) is int:
                key = cuts[key]
            vspec.sq_row(key)            # validates the key
            out.append((key, Fr(t[1])))
        return out
    for i, rec in enumerate(recs):
        if rec[0] == "K":
            if len(rec) != 3 or type(rec[1]) is not int or rec[1] in cuts:
                raise AssertionError(f"bad K record in {f}")
            vspec.sq_row(rec[2])
            cuts[rec[1]] = rec[2]
            continue
        rg, pth = stack.pop()
        kind = rec[0]
        nrec += 1
        if kind == "I":
            b, s = rec[1], Fr(rec[2])
            c0, k0 = fchild(tree, rg, b, float(s), 0)
            c1, k1 = fchild(tree, rg, b, float(s), 1)
            if c0 is None or c1 is None:
                raise AssertionError(f"empty child in {f}: not supported by the kernel checker")
            sv = s * (1 << SB)
            assert sv.denominator == 1 and 0 < sv.numerator < (1 << 31) and b < 128 and k0 < 16 and k1 < 16
            parts.append(((b << 2) | (sv.numerator << 9) | (k0 << 40) | (k1 << 44), 48))
            stack.append((c0, pth + [(b, s, 0)])); stack.append((c1, pth + [(b, s, 1)]))
        elif kind == "L":
            if len(rec) not in (4, 5):
                raise AssertionError(f"bad L record in {f}")
            duals = split_big(kc_ref.kc_duals(ks, rowkeys, rec[2], rec[3]))
            cdu = kc_ref.kc_cut_duals(resolve(rec[4])) if len(rec) == 5 else []
            ok, lb = kc_ref.kc_accept(ks, lam, [Fr(x) for x in rg[0]], [Fr(x) for x in rg[1]], duals + cdu)
            if not ok:
                raise AssertionError(f"KC re-check failed in {f}: {float(lb)}")
            cnt = len(duals) + 2 * len(cdu)         # a cut record occupies two 87-bit chunks
            assert cnt < 16384
            parts.append((1 | (cnt << 2), 16))
            for key, Y in duals:
                assert 0 < abs(Y) < (1 << 72)
                parts.append((rindex[key] | ((1 if Y < 0 else 0) << 14) | (abs(Y) << 15), 87))
            for (_, v0, d, v1, e, v2), M in cdu:       # cut record (AutocorrK.loop: escape 16383, 174 bits)
                assert 0 < M < (1 << 64) and d < 128 and e < 128
                x = 16383 | (d << 15) | (e << 22)
                for off, v in ((29, v0), (51, v1), (73, v2)):
                    assert abs(v) < (1 << 21)
                    x |= ((1 if v < 0 else 0) | (abs(v) << 1)) << off
                parts.append((x | (M << 95), 174))
            nleaves += 1; nl_seg += 1
        elif kind == "S":
            parts.append((2, 2))
            dels.append((path_key(pth), pk_box(rg)))
        else:
            raise AssertionError(f"record {kind} not supported by the kernel checker ({f})")
        if (nl_seg >= seg_leaves and i < last) or i == last:
            segs.append((nrec, pack(parts), dels, [pk_box(r) for r, _ in reversed(stack)]))
            parts, nrec, nl_seg, dels = [], 0, 0, []
    if stack:
        raise AssertionError(f"nodes left in {f}")
    return path_key(path), pk_box(reg), segs, nleaves, os.path.basename(f)


def init_worker(n, rowkeys, lam, seg_leaves):
    spec = verify.Spec(n)
    G["tree"] = spec.tree
    G["ks"] = kc_ref.KSpec(n)
    G["vspec"] = verify_cmp.Spec(n)
    G["rowkeys"] = rowkeys
    G["rindex"] = {k: i for i, k in enumerate(rowkeys)}
    G["lam"] = lam
    G["seg_leaves"] = seg_leaves
    G["root"], _ = fprop(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)
    G["nB"] = spec.nB


def scan(f):
    pk, _, segs, nl, _ = kc_job(f, G["seg_leaves"])
    return pk, [c for s in segs for c, _ in s[2]], nl, len(segs), f


def lbox(bx):
    return f"(nat_b64% \"{b64(bx[0])}\", nat_b64% \"{b64(bx[1])}\")"


def write_file(fn, src):
    old = open(fn).read() if os.path.exists(fn) else None
    if old != src:
        os.makedirs(os.path.dirname(fn), exist_ok=True)
        with open(fn, "w") as fh:
            fh.write(src)
        return 1
    return 0


def write_group(task):
    """Two modules per group: the kernel checks (imports only Params, so all of them build in parallel) and
    the assembly of the jobs' StkK statements (imports the checks and the children's assembly modules)."""
    gid, jobs, fn_c, fn_g, header_c, header_g, footer = task
    a, b = G["lam"].numerator, G["lam"].denominator
    pc, pg = [header_c], [header_g]
    for (k, f, kids) in jobs:
        pk, rootbox, segs, nl, fname = kc_job(f, G["seg_leaves"])
        kid = dict(kids)
        allc = [c for s in segs for c, _ in s[2]]
        assert allc == [c for c, _ in kids], f"pass 2 disagrees with pass 1 for {fname}"
        nrecs = sum(s[0] for s in segs)
        out = [f"\n-- job {fname}: {nl} leaves, {nrecs} records, {len(kids)} delegated, {len(segs)} segments\n",
               f"def jb{k} : Nat × Nat := {lbox(rootbox)}\n"]
        sin = f"[jb{k}]"
        term, closes = "", 0
        for i, (nrec, data, dels, stk) in enumerate(segs, 1):
            if i < len(segs):
                w = 32 * G["nB"]
                lit = pack([(lo | (up << w), 2 * w) for lo, up in stk])
                out.append(f"def js{k}_{i} : List (Nat × Nat) := AutocorrK.unpk {w} {len(stk)} (nat_b64% \"{b64(lit)}\")\n")
                rest = f"js{k}_{i}"
            else:
                assert not stk
                rest = "[]"
            for c, bx in dels:      # the delegated box as computed here; jfull<c> proves it for jb<c> (defeq)
                out.append(f"def jq{kid[c]} : Nat × Nat := {lbox(bx)}\n")
            sout = "".join(f"jq{kid[c]} :: " for c, _ in dels) + rest
            out.append(f"def jd{k}_{i} : Nat := nat_b64% \"{b64(data)}\"\n")
            out.append(f"theorem jc{k}_{i} : AutocorrK.segCheck P {a} {b} {nrec} jd{k}_{i} {sin} ({sout}) = true := "
                       f"by decide +kernel\n")
            term += f".seg _ _ jc{k}_{i} (" + "".join(f".cons jfull{kid[c]} (" for c, _ in dels)
            closes += len(dels) + 1
            sin = rest
        term += ".nil" + ")" * closes
        pc.append("".join(out))
        pg.append(f"\ntheorem jfull{k} : AutocorrK.StkK P {a} {b} [jb{k}] :=\n  {term}\n")
    pc.append(footer); pg.append(footer)
    return write_file(fn_c, "".join(pc)) + write_file(fn_g, "".join(pg))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("pkg")
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--group-leaves", type=int, default=0)
    ap.add_argument("--seg-leaves", type=int, default=16)
    args = ap.parse_args()
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [tuple(spec.validate_key(tuple(k))) for k in meta["rowkeys"]]
    files = sorted(glob.glob(os.path.join(args.certdir, "jobs", "*.jsonl.gz")))
    ctx = get_context("fork")
    iargs = (n, rowkeys, lam, args.seg_leaves)
    t0 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=init_worker, initargs=iargs) as pool:
            res = pool.map(scan, files, chunksize=4)
    else:
        init_worker(*iargs)
        res = [scan(f) for f in files]
    print(f"pass 1 (exact KC re-check of every leaf): {len(res)} jobs in {time.time()-t0:.1f}s", flush=True)
    res.sort(key=lambda r: (len(r[0]), r[0]))
    assert res[0][0] == (), "no root job"
    idx = {r[0]: k for k, r in enumerate(res)}
    assert len(idx) == len(res), "duplicate job roots"
    kids = [[(c, idx[c]) for c in r[1]] for r in res]
    used = [c for ks in kids for c, _ in ks]
    assert len(used) == len(set(used)) == len(res) - 1, "delegation is not a tree"
    nleaf = [r[2] for r in res]
    order = []
    st = [(0, False)]
    while st:
        k, done = st.pop()
        if done:
            order.append(k); continue
        st.append((k, True))
        for _, c in kids[k]:
            st.append((c, False))
    assert len(order) == len(res), "orphan jobs"
    tot = [0] * len(res)
    for k in order:
        tot[k] = nleaf[k] + sum(tot[c] for _, c in kids[k])
    group = [None] * len(res)
    st = [0]
    while st:
        k = st.pop()
        if tot[k] <= args.group_leaves:
            sub = [k]; i = 0
            while i < len(sub):
                sub.extend(c for _, c in kids[sub[i]]); i += 1
            for j in sub:
                group[j] = k
        else:
            group[k] = k
            st.extend(c for _, c in kids[k])
    ns = f"Autocorr.{args.pkg}"
    base = os.path.join(args.root, "Autocorr", args.pkg)
    os.makedirs(base, exist_ok=True)

    def modname(g, d="G"):
        return f"{ns}.{d}{g // 1000:03d}.{d}{g:06d}"

    def modfile(g, d="G"):
        return os.path.join(base, f"{d}{g // 1000:03d}", f"{d}{g:06d}.lean")
    members = {}
    for k in order:                      # post-order: children before parents
        members.setdefault(group[k], []).append(k)
    tasks = []
    opts = "set_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 100000\n"
    for g, ksl in members.items():
        imps = sorted({group[c] for k in ksl for _, c in kids[k] if group[c] != g})
        info = f"-- group of {len(ksl)} jobs, {sum(nleaf[k] for k in ksl)} leaves\n"
        header_c = (f"import {ns}.Params\n\n" + info + "-- kernel checks of the segments\n" + opts +
                    f"\nnamespace {ns}\n\nnoncomputable section\n")
        header_g = (f"import {modname(g, 'C')}\n" + "".join(f"import {modname(h)}\n" for h in imps) + "\n" + info +
                    "-- assembly of the jobs' coverage statements\n" + opts + f"\nnamespace {ns}\n\nnoncomputable section\n")
        footer = f"\nend\n\nend {ns}\n"
        tasks.append((g, [(k, res[k][4], kids[k]) for k in ksl], modfile(g, "C"), modfile(g), header_c, header_g, footer))
    t1 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=init_worker, initargs=iargs) as pool:
            nw = sum(pool.imap_unordered(write_group, tasks, chunksize=1))
    else:
        nw = sum(write_group(t) for t in tasks)
    print(f"pass 2: wrote {nw} of {2 * len(tasks)} modules in {time.time()-t1:.1f}s", flush=True)
    kp, _ = KE.kp_constants(n, rowkeys)
    rootf, K0 = fprop(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)
    UP = sum((1 << 30) << (32 * b) for b in range(spec.nB))
    a, b = lam.numerator, lam.denominator
    params = f"""import AutocorrK.Stk
import AutocorrK.Table
import AutocorrK.Load

/-! Constants of the kernel checker for n = {n} and their one-time kernel check against `mkSpec {n}`. -/

set_option Elab.async false

namespace {ns}

noncomputable def P : AutocorrK.KP := ⟨{kp['n']}, {kp['nB']}, {kp['oZ']}, {kp['oP']}, {kp['oG']}, {kp['NC1']}, {kp['NR']},
  nat_b64% "{b64(kp['T'])}", nat_b64% "{b64(kp['symP'])}", nat_b64% "{b64(kp['symN'])}",
  nat_b64% "{b64(kp['intTab'])}", {kp['nInt']}, nat_b64% "{b64(kp['canonTab'])}"⟩

theorem kpok : AutocorrK.kpOK (Autocorr.Cert.mkSpec {n}) P = true := by decide +kernel

end {ns}
"""
    fn = os.path.join(base, "Params.lean")
    if not os.path.exists(fn) or open(fn).read() != params:
        open(fn, "w").write(params)
    main_src = f"""import {modname(group[0])}
import Autocorr.KSound.Run
import Autocorr.Reduction

/-!
# The certificate `{os.path.basename(os.path.normpath(args.certdir))}` (n = {n}, lam = {a}/{b}) checked by the Lean kernel

{len(res)} jobs, {sum(nleaf)} leaves, in 2 x {len(tasks)} core-only modules; every segment of the DFS log is a
`decide +kernel` check of `AutocorrK.segCheck` (no native code), composed by `AutocorrK.StkK`.
-/

open MeasureTheory ENNReal Set

namespace {ns}

noncomputable def UP : ℕ := nat_b64% "{b64(UP)}"

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P {K0} 0 UP = jb0 := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec {n}) P := AutocorrK.kpFacts kpok

theorem halfClaim : HalfClaim {n} ((({a} : ℕ) : ℝ) / (({b} : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull0).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec {n}).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec {n}).n = {n} := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

lemma ofReal_lam : ENNReal.ofReal ((({a} : ℕ) : ℝ) / (({b} : ℕ) : ℝ)) = ({a} / {b} : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ {a}/{b}`: for every measurable `f : ℝ → [0, ∞]`,
`{a}/{b} · (∫_{{-1/4}}^{{1/4}} f)² ≤ sup_{{t ∈ [-1/2, 1/2]}} ∫ f(t - x) f(x) dx` (kernel-checked certificate). -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ({a} / {b} : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

end {ns}
"""
    fn = os.path.join(base, "Main.lean")
    if not os.path.exists(fn) or open(fn).read() != main_src:
        open(fn, "w").write(main_src)
    nseg = sum(r[3] for r in res)
    json.dump({"n": n, "lam": str(lam), "jobs": len(res), "modules": len(tasks), "leaves": sum(nleaf),
               "segments": nseg, "K0": K0, "root_module": modname(group[0]), "seg_leaves": args.seg_leaves,
               "group_leaves": args.group_leaves}, open(os.path.join(base, "export.json"), "w"))
    print(f"{len(res)} jobs, {len(tasks)} modules, {nseg} segments, {sum(nleaf)} leaves under {base}")


if __name__ == "__main__":
    main()
