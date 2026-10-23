"""Sharded export for the kernel checker (AutocorrK), as tools/export_shard.py is for the native checker.

Same modules as tools/kc_jobs.py (imported: its pass 1, kc_job, segment encoding and Params/Main text are reused), but
jobs and modules are named by job file id instead of a global index, so that disjoint sets of jobs can be exported and
built on different machines and composed afterwards:

    def jb_<id>, js_<id>_<i>, jd_<id>_<i>, theorem jc_<id>_<i>     (check module of the group, imports only Params)
    def jq_<id>                                                   (in the check module of the PARENT of job <id>)
    theorem jfull_<id> : AutocorrK.StkK P a b [jb_<id>]           (assembly module of the group)
    check module    Autocorr.PKG.C<gid[:2]>.C<gid>,   assembly module  Autocorr.PKG.G<gid[:2]>.G<gid>

usage: kc_shard.py CERTDIR PKG [--workers W] [--group-leaves G] [--seg-leaves S] [--external EXT.json] [--main]
                   [--single-group]
  CERTDIR   meta.json + jobs/*.jsonl.gz (filled format-2 jobs): complete delegation subtrees (a build shard), or the
            jobs near the root (the assembly shard, with EXT.json naming the roots of the subtrees built elsewhere).
  EXT.json  {"<json list of the root path key>": "<job id>", ...}; every external subtree root roots its own group,
            so its assembly module is Autocorr.PKG.G<id[:2]>.G<id>.
  --main    write Main.lean (needs the job with the empty root path); --single-group: one group for all local jobs.
Params.lean is the same text for every shard of the same certificate.  Nothing here is trusted (see kc_jobs.py).
"""
import sys, os, json, glob, argparse, time
from fractions import Fraction as Fr
from multiprocessing import get_context

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kc_jobs as KJ        # noqa: E402  (G, kc_job, init_worker, scan, lbox, write_file, b64, pack, fprop, KE, verify)


def jid(f):
    b = os.path.basename(f)
    assert b.endswith(".jsonl.gz")
    return b[:-len(".jsonl.gz")]


def write_group_id(task):
    gid, jobs, fn_cs, fn_g, header_c, header_g, footer, chunk_of = task
    G = KJ.G
    a, b = G["lam"].numerator, G["lam"].denominator
    pcs, pg = [[header_c] for _ in fn_cs], [header_g]
    for (k, f, kids) in jobs:                    # kids: [(child path key, child job id)]
        pc = pcs[chunk_of.get(k, 0)]
        pk, rootbox, segs, nl, fname = KJ.kc_job(f, G["seg_leaves"])
        kid = dict(kids)
        allc = [c for s in segs for c, _ in s[2]]
        assert allc == [c for c, _ in kids], f"pass 2 disagrees with pass 1 for {fname}"
        nrecs = sum(s[0] for s in segs)
        out = [f"\n-- job {fname}: {nl} leaves, {nrecs} records, {len(kids)} delegated, {len(segs)} segments\n",
               f"def jb_{k} : Nat × Nat := {KJ.lbox(rootbox)}\n"]
        sin = f"[jb_{k}]"
        term, closes = "", 0
        for i, (nrec, data, dels, stk) in enumerate(segs, 1):
            if i < len(segs):
                w = 32 * G["nB"]
                lit = KJ.pack([(lo | (up << w), 2 * w) for lo, up in stk])
                out.append(f"def js_{k}_{i} : List (Nat × Nat) := AutocorrK.unpk {w} {len(stk)} "
                           f"(nat_b64% \"{KJ.b64(lit)}\")\n")
                rest = f"js_{k}_{i}"
            else:
                assert not stk
                rest = "[]"
            for c, bx in dels:      # the delegated box as computed here; jfull_<c> proves it for jb_<c> (defeq)
                out.append(f"def jq_{kid[c]} : Nat × Nat := {KJ.lbox(bx)}\n")
            sout = "".join(f"jq_{kid[c]} :: " for c, _ in dels) + rest
            out.append(f"def jd_{k}_{i} : Nat := nat_b64% \"{KJ.b64(data)}\"\n")
            out.append(f"theorem jc_{k}_{i} : AutocorrK.segCheck P {a} {b} {nrec} jd_{k}_{i} {sin} ({sout}) = true := "
                       f"by decide +kernel\n")
            term += f".seg _ _ jc_{k}_{i} (" + "".join(f".cons jfull_{kid[c]} (" for c, _ in dels)
            closes += len(dels) + 1
            sin = rest
        term += ".nil" + ")" * closes
        pc.append("".join(out))
        pg.append(f"\ntheorem jfull_{k} : AutocorrK.StkK P {a} {b} [jb_{k}] :=\n  {term}\n")
    pg.append(footer)
    n = KJ.write_file(fn_g, "".join(pg))
    for fn_c, pc in zip(fn_cs, pcs):
        pc.append(footer)
        n += KJ.write_file(fn_c, "".join(pc))
    return n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("pkg")
    ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--group-leaves", type=int, default=0)
    ap.add_argument("--seg-leaves", type=int, default=16)
    ap.add_argument("--external", default=None)
    ap.add_argument("--main", action="store_true")
    ap.add_argument("--single-group", action="store_true")
    ap.add_argument("--split-checks", type=int, default=0,
                    help="split a group's kernel checks into C modules of at most this many leaves (parallel builds); "
                         "its G module imports all of them (for a large single-group assembly)")
    args = ap.parse_args()
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = KJ.verify.Spec(n)
    rowkeys = [tuple(spec.validate_key(tuple(k))) for k in meta["rowkeys"]]
    files = sorted(glob.glob(os.path.join(args.certdir, "jobs", "*.jsonl.gz")))
    ext = {}
    if args.external:
        for kj, v in json.load(open(args.external)).items():
            ext[tuple((int(x[0]), str(x[1]), int(x[2])) for x in json.loads(kj))] = v
    ctx = get_context("fork")
    iargs = (n, rowkeys, lam, args.seg_leaves)
    t0 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=KJ.init_worker, initargs=iargs) as pool:
            res = pool.map(KJ.scan, files, chunksize=4)
    else:
        KJ.init_worker(*iargs)
        res = [KJ.scan(f) for f in files]
    print(f"pass 1 (exact KC re-check of every leaf): {len(res)} jobs in {time.time()-t0:.1f}s", flush=True)
    ids = [jid(r[4]) for r in res]
    assert len(set(ids)) == len(ids), "duplicate job ids"
    bykey = {r[0]: i for i, r in enumerate(res)}
    assert len(bykey) == len(res), "duplicate job roots"
    used = set()
    kids, kid_local, ext_used = [], [], set()
    for k, r in enumerate(res):
        ki, kl = [], []
        for c in r[1]:
            assert c not in used, "path delegated twice"
            used.add(c)
            if c in bykey:
                ki.append((c, ids[bykey[c]])); kl.append(bykey[c])
            elif c in ext:
                ki.append((c, ext[c])); ext_used.add(c)
            else:
                raise AssertionError(f"delegated path without job (job {ids[k]})")
        kids.append(ki); kid_local.append(kl)
    assert not (set(ext) - ext_used), "external subtree roots not delegated by any job of this shard"
    roots = [i for i, r in enumerate(res) if r[0] not in used]
    if args.main:
        assert () in bykey and roots == [bykey[()]], "--main needs exactly one local root, the empty path"
    nleaf = [r[2] for r in res]
    order = []
    for r0 in roots:
        st = [(r0, False)]
        while st:
            k, done = st.pop()
            if done:
                order.append(k); continue
            st.append((k, True))
            st.extend((c, False) for c in kid_local[k])
    assert len(order) == len(res), "jobs not reachable from the shard roots"
    tot = [0] * len(res)
    for k in order:
        tot[k] = nleaf[k] + sum(tot[c] for c in kid_local[k]) + (10 ** 18 if len(kid_local[k]) != len(kids[k]) else 0)
    group = [None] * len(res)
    if args.single_group:
        assert len(roots) == 1, "--single-group needs exactly one local root"
        group = [roots[0]] * len(res)
        st = []
    else:
        st = list(roots)
    while st:                          # every shard root roots its own group (external references rely on this)
        k = st.pop()
        if tot[k] <= args.group_leaves:
            sub = [k]; i = 0
            while i < len(sub):
                sub.extend(kid_local[sub[i]]); i += 1
            for j in sub:
                group[j] = k
        else:
            group[k] = k
            st.extend(kid_local[k])
    ns = f"Autocorr.{args.pkg}"
    base = os.path.join(args.root, "Autocorr", args.pkg)
    os.makedirs(base, exist_ok=True)

    def modname(gid, d="G"):
        return f"{ns}.{d}{gid[:2]}.{d}{gid}"

    def modfile(gid, d="G"):
        return os.path.join(base, f"{d}{gid[:2]}", f"{d}{gid}.lean")
    members = {}
    for k in order:                      # post-order: children before parents
        members.setdefault(group[k], []).append(k)
    tasks = []
    opts = "set_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 100000\n"
    for g, ksl in members.items():
        imps = set()
        for k in ksl:
            for c in kid_local[k]:
                if group[c] != g:
                    imps.add(ids[group[c]])
            for c, cid in kids[k]:
                if c in ext_used:
                    imps.add(cid)
        info = f"-- group of {len(ksl)} jobs, {sum(nleaf[k] for k in ksl)} leaves\n"
        header_c = (f"import {ns}.Params\n\n" + info + "-- kernel checks of the segments\n" + opts +
                    f"\nnamespace {ns}\n\nnoncomputable section\n")
        chunk_of, nch, acc = {}, 1, 0
        if args.split_checks and sum(nleaf[k] for k in ksl) > args.split_checks:
            nch = 0; acc = args.split_checks
            for k in ksl:
                if acc + nleaf[k] > args.split_checks and acc > 0:
                    nch += 1; acc = 0
                chunk_of[ids[k]] = nch - 1; acc += nleaf[k]
        cmods = [modname(ids[g], "C")] if nch == 1 else [modname(ids[g], "C") + f"_{i}" for i in range(nch)]
        cfiles = [modfile(ids[g], "C")] if nch == 1 else [modfile(ids[g], "C")[:-5] + f"_{i}.lean" for i in range(nch)]
        header_g = ("".join(f"import {m}\n" for m in cmods) + "".join(f"import {modname(h)}\n" for h in sorted(imps)) +
                    "\n" + info + "-- assembly of the jobs' coverage statements\n" + opts +
                    f"\nnamespace {ns}\n\nnoncomputable section\n")
        footer = f"\nend\n\nend {ns}\n"
        tasks.append((ids[g], [(ids[k], res[k][4], kids[k]) for k in ksl], cfiles, modfile(ids[g]),
                      header_c, header_g, footer, chunk_of))
    t1 = time.time()
    if args.workers > 1:
        with ctx.Pool(args.workers, initializer=KJ.init_worker, initargs=iargs) as pool:
            nw = sum(pool.imap_unordered(write_group_id, tasks, chunksize=1))
    else:
        nw = sum(write_group_id(t) for t in tasks)
    print(f"pass 2: wrote {nw} of {2 * len(tasks)} modules in {time.time()-t1:.1f}s", flush=True)
    kp, _ = KJ.KE.kp_constants(n, rowkeys)
    b64 = KJ.b64
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
    KJ.write_file(os.path.join(base, "Params.lean"), params)
    info = {"n": n, "lam": str(lam), "jobs": len(res), "modules": 2 * len(tasks), "leaves": sum(nleaf),
            "segments": sum(r[3] for r in res), "roots": [ids[r] for r in roots],
            "root_modules": [modname(ids[r]) for r in roots], "seg_leaves": args.seg_leaves,
            "group_leaves": args.group_leaves}
    if args.main:
        root = ids[roots[0]]
        rootf, K0 = KJ.fprop(spec.tree, [0.0] * spec.nB, [1.0] * spec.nB)
        UP = sum((1 << 30) << (32 * bb) for bb in range(spec.nB))
        main_src = f"""import {modname(root)}
import Autocorr.KSound.Run
import Autocorr.Reduction

/-!
# The certificate `{os.path.basename(os.path.normpath(args.certdir))}` (n = {n}, lam = {a}/{b}) checked by the Lean kernel

Composed from sharded modules (tools/kc_shard.py): every segment of every job's DFS log is a `decide +kernel` check
of `AutocorrK.segCheck` (no native code), composed by `AutocorrK.StkK`.
-/

open MeasureTheory ENNReal Set

namespace {ns}

noncomputable def UP : ℕ := nat_b64% "{b64(UP)}"

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P {K0} 0 UP = jb_{root} := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec {n}) P := AutocorrK.kpFacts kpok

theorem halfClaim : HalfClaim {n} ((({a} : ℕ) : ℝ) / (({b} : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull_{root}).head
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
        KJ.write_file(os.path.join(base, "Main.lean"), main_src)
        info["K0"] = K0
    json.dump(info, open(os.path.join(base, "kc_shard.json"), "w"))
    print(f"{len(res)} jobs, {2 * len(tasks)} modules, {info['segments']} segments, {sum(nleaf)} leaves under {base}")


if __name__ == "__main__":
    main()
