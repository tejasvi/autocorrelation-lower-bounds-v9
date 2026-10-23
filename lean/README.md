# Lean 4 formalization of the lower bounds for the first autocorrelation constant

This directory contains Lean 4 proofs, built on Mathlib, of the following statement for six values of λ:

    λ · (∫_{−1/4}^{1/4} f)²  ≤  sup_{|t| ≤ 1/2} ∫ f(t − x) f(x) dx      for every measurable f : ℝ → [0, ∞].

The values are λ = 267/200, 133/100, 33/25, 131/100, 13/10 and 32/25. The largest gives C₁ ≥ 1.335 for the first
autocorrelation constant (Problem 6.2 of arXiv:2511.02864). Each proof combines two parts:

* a certificate-independent part: the reduction to a finite claim about bin masses, and the soundness of the
  checkers;
* a mechanical check of one certificate.

The certificate check comes in two variants:

* compiled code run through `native_decide`, with a checker that uses exact rational arithmetic;
* the Lean kernel alone, through `decide +kernel`, with a checker that uses only natural-number arithmetic.

## What is proved

For a certificate with λ = a/b, the generated package `P` proves three theorems.

```lean
theorem Autocorr.P.autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (a / b : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x

theorem Autocorr.P.autocorr_lower_ess (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (a / b : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2)))

theorem Autocorr.P.autocorr_lower_real (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal (a / b * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2)))
```

* `autocorr_lower` is the statement above, written with the Lebesgue integral `∫⁻`.
* `autocorr_lower_ess` bounds the essential supremum of `f ⋆ f` on `[−1/2, 1/2]`, that is its L^∞ norm there.
  It is the stronger form, because `Autocorr.essSup_conv_le_iSup` shows that the essential supremum is at most
  the pointwise supremum.
* `autocorr_lower_real` is the version for real-valued `f`. It uses Mathlib's convolution
  `(f ⋆ f)(t) = ∫ f(s) f(t − s) ds` and the L^∞ norm, valued in `[0, ∞]`. The proof relates the Bochner
  integrals to Lebesgue integrals. If `f` is not integrable, `∫ f` is `0` by Mathlib's convention and the
  statement holds trivially.

The certificate-independent lemmas are generic in n and λ:

* `Autocorr.autocorr_lower_of_halfClaim`
* `Autocorr.autocorr_lower_ess_of_halfClaim`
* `Autocorr.autocorr_lower_real_of_halfClaim`

| package | λ | certificate | check | theorems | `#print axioms` |
|---|---|---|---|---|---|
| `C39T` | 267/200 | c39t (n = 39, the logs of the search, with the dual vectors written by `verify_tree_dump.py` for its tree-only leaves) | `native_decide` | all three | the 3 standard axioms + 13,678,677 `native_decide` axioms |
| `C36T` | 133/100 | c36t (n = 36, tree-only, with the dual vectors written by `verify_tree_dump.py`) | `native_decide` | all three | the 3 standard axioms + 2,419,680 `native_decide` axioms |
| `C30` | 33/25 | c30_132m (n = 30, format 2) | `native_decide` | all three | the 3 standard axioms + 290,309 `native_decide` axioms |
| `KC28` | 131/100 | c28_131 (n = 28) | kernel | all three | **propext, Classical.choice, Quot.sound** |
| `C28` | 131/100 | c28_131 | `native_decide` | `autocorr_lower` | the 3 standard axioms + 322,267 `native_decide` axioms |
| `C24` | 13/10 | c24_130 (n = 24) | `native_decide` | `autocorr_lower` | the 3 standard axioms + 13,975 `native_decide` axioms |
| `C20` | 32/25 | c20_128 (n = 20) | `native_decide` | all three | the 3 standard axioms + 426 `native_decide` axioms |
| `KC20` | 32/25 | c20_128 | kernel | `autocorr_lower` | **propext, Classical.choice, Quot.sound** |

The `#print axioms` output for each package is in `results/<package>/`, together with `Main.lean`, `Forms.lean`
(where built), a run summary (`summary.txt`) and the per-module build times. No proof uses `sorry`.

## Trusted base

* **`native_decide` packages.** The trusted base includes Lean's compiler and the compiled checker
  (`AutocorrCert/`). Every use of `native_decide` adds one axiom of the form
  `X._native.native_decide.ax_1_1 : decide P = true`. There is one per job of the certificate and one for the
  root region (`rootOK`). `#print axioms` lists them all.
* **Kernel packages (`KC20`, `KC28`).** Only the Lean kernel is trusted. It evaluates every check through
  `decide +kernel`, and the theorems depend on the three standard axioms only.
* **In both variants the exporters and all generated data are untrusted.** The theorem statement does not
  mention the certificate. A wrong box, multiplier or split value makes a check fail; it cannot produce a wrong
  theorem.

## Contents

* `Autocorr/Defs.lean`, `Analytic.lean`, `Reversal.lean`, `Reduction.lean`, `RealForm.lean`. The reduction:
  - bins and the Cloninger–Steinerberger window lemma (Tonelli and translation invariance);
  - homogeneity, with the cases of infinite and zero mass;
  - the reversal symmetry, so that a certificate only has to cover the half-space Σ(2i − (n−1)) p_i ≤ 0.
* `AutocorrCert/Checker.lean`, `Decode.lean`. The native checker for format 1 (`checker/verify.py`): the block
  tree, interval propagation, the linear constraints rebuilt from their keys, the Neumaier–Shcherbina bound, and a
  stack machine over the job logs.
* `AutocorrCert/CheckerX.lean`, `DecodeX.lean`. The native checker for format 2 (`checker/verify_cmp.py`), with
  square-cut rows and compressed leaves. For a compressed leaf the checker computes the missing multipliers of
  the equality rows itself; that computation is untrusted, since the bound is checked for whatever vector
  results.
* `Autocorr/Cert/*.lean`. Soundness of the native checkers: validity of every row type, weak duality, the
  stack machine, and the job composition `halfClaim_of_covered` / `halfClaim_of_coveredX`.
* `AutocorrK/*.lean`. The kernel checker:
  - natural numbers only, with reduced costs split by sign into packed 136-bit digits;
  - packed boxes and interval propagation in the kernel;
  - a one-time check of the constraint table against the block tree (`kpOK`);
  - `StkK`, which composes the segment checks.
* `Autocorr/KSound/*.lean`. Soundness of the kernel checker (`AutocorrK.stkK_sound`,
  `AutocorrK.halfClaim_of_rootK`).
* `tools/`. Exporters, the build scheduler, the run scripts and `cert_manifest.py` (certificate fingerprints); for
  `C36T` and `C39T` also the sharded exporter `export_shard.py` (with `--pack` for `C39T`), `shard_map.py`, `merge_top.py`,
  `prefetch_olean.py`, the axiom scanners `nscan.lean` and `nscan_ext.lean`, and the dump verifier
  `tree/verify_tree_dump_34da7947.py`.
* `examples/`. Two small certificates: `cert_test8` (n = 8, λ = 59/50) and `t12m3` (n = 12, λ = 49/40,
  format 2).
* `results/`. Records of the runs listed above.

## Requirements

* The Lean toolchain named in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc3`, installed by `elan`) and
  Mathlib at tag `v4.35.0-rc3` (commit c55e6e786f49…, pinned in `lake-manifest.json`).
* Python 3 (standard library only) for the exporters. They import the Python checkers `verify.py` and
  `verify_cmp.py` from `../checker`. If the checkers are elsewhere, set `AUTOCORR_CHECKER` to their directory.

Building the certificate-independent part:

    lake exe cache get      # Mathlib's compiled files
    lake build              # the reduction, both checkers and their soundness proofs

## Worked example

    tools/example.sh 8      # 8 parallel workers

This builds three small packages and writes logs and `#print axioms` output to `examples/out/<package>/`:

| package | proof |
|---|---|
| `KT8` | kernel-only proof of V_8 ≥ 59/50 from `examples/cert_test8` |
| `T8` | `native_decide` proof of V_8 ≥ 59/50 from `examples/cert_test8` |
| `X12` | `native_decide` proof of V_12 ≥ 49/40 from the format-2 certificate `examples/t12m3` |

After `lake build` it takes a few minutes. `KT8` depends on the three standard axioms only.

## Regenerating the proof of C₁ ≥ 1.335 (`C39T`)

Input: the job logs of the certificate `c39t` (meta.json sha256 4b330edc…), whose leaves are mostly explicit dual
vectors (D records, completed by the checker in Lean); the 415,366 tree-only leaves are replaced by the exact duals
that the frozen dump verifier `tools/tree/verify_tree_dump_34da7947.py` accepted (`VT_DUMP_DIR`).
The list of the 13,678,676 input files (sha256, size, name) is in the Zenodo record as
`c39t_filled_certificate.sha256.gz` (824,360,082 bytes); the sha256 of the uncompressed list is
d5de36f2fb93278f4e0a0bb2ca3cebf39cae90dd33186cca395b4f62587fb71e. These files (1,422,711,357,387 bytes) are not
archived. Running the dump verifier on the archive `c39t_V39_1335_certificate.tar.zst` produces a filled certificate in
which every leaf carries a dual vector, as for `C36T`; its duals differ from those used here, and any filled certificate
that the Lean checker accepts gives the theorem.

Regeneration and build (the run used 137 shard machines and one assembly machine):

    # shards: complete delegation subtrees; for each shard a certdir with meta.json + its job files, then
    python3 tools/export_shard.py SHARD C39T --workers W --pack --group-leaves 3000 --skip-unchanged
    python3 tools/build_dag.py . C39T --jobs J --rm-src --dynlib ... (the four AutocorrCert dynlibs)
    # assembly (the jobs near the root), EXT.json mapping each subtree root's encoded path to its job id:
    python3 tools/export_shard.py ASM C39T --external EXT.json --main --single-group
    python3 tools/forms.py C39T 39 267 200
    python3 tools/merge_top.py . C39T --split-checks 64
    python3 tools/build_dag.py . C39T --jobs 64 --exclude TOP.txt --dynlib ...   # Zo + the 64 check chunks
    python3 tools/prefetch_olean.py OLEANS.txt 128     # load the pages the import reads (all .olean of the package)
    lean -o .lake/build/lib/lean/Autocorr/C39T/Gro/Groot.olean Autocorr/C39T/Gro/Groot.lean
    # axioms: per-module scan of every .olean, then the axioms of the external references
    lean --run tools/nscan.lean LIST OUT Autocorr.C39T.
    KSCAN_EXT=external.txt lean tools/nscan_ext.lean

New tools: `export_shard.py --pack` (bottom-up packing of jobs into modules of about `--group-leaves` leaves; the
previous grouping made every job above a full-size subtree its own module), `prefetch_olean.py` (reads, for every
.olean, the pages that Lean's import touches: the header, the root module data, its arrays and every ConstantInfo;
on a 153-module closure the cold import went from 7,163 major page faults to 5), `nscan.lean` / `nscan_ext.lean`
(per-module axiom scan without importing the closure: only native_decide auxiliary axioms of the package may be
declared, and their types must be `decide p = true`; the axioms of the external references come from a library-only
session). Axioms of `autocorr_lower`, `autocorr_lower_ess`, `autocorr_lower_real`: propext, Classical.choice,
Quot.sound and 13,678,677 native_decide auxiliary axioms (one per job, plus the root box).

## Regenerating the proof of C₁ ≥ 1.33 (`C36T`)

Input: the filled certificate written by the frozen dump verifier `tools/tree/verify_tree_dump_34da7947.py`
(with `VT_DUMP_DIR` set) while it verifies the tree-only certificate `c36t` (meta.json sha256 9a8362d5…): every
job file of the certificate with each accepted leaf replaced by the exact dual the check accepted.
The filled certificate (2,419,679 files, 2,118.5 GB) is not archived; running the dump verifier on the archive
`c36t_V36_133_certificate.tar` produces one (its duals may differ between machines; any filled certificate that the
Lean checker accepts gives the theorem). The list of the files used here (sha256, size, name) is in the Zenodo record as
`c36t_filled_certificate.sha256.gz` (147,520,513 bytes); the sha256 of the uncompressed list is
39cc003ed01a8b528bc0b615e07d8774074b9fa6c96aceaeecdeeba9adfd245c (`results/C36T/export.json`).

Regeneration and build (one machine shown; the run used 202 machines, one shard each, and one assembly machine):

    python3 tools/shard_map.py CERT 202 shardmap.json        # complete delegation subtrees -> shards + assembly
    # for each shard: a certdir with meta.json + the shard's filled jobs/, then
    python3 tools/export_shard.py SHARD C36T --workers W --skip-unchanged
    python3 tools/build_dag.py . C36T --jobs J --rm-src --dynlib ... (the four AutocorrCert dynlibs, as in run_m3x.sh)
    # assembly (the 620 jobs near the root), with EXT.json = shardmap.json["external"]:
    python3 tools/export_shard.py ASM C36T --external EXT.json --main --single-group
    python3 tools/forms.py C36T 36 133 100
    python3 tools/merge_top.py . C36T --split-checks 64 --report-dir DIR
    python3 tools/build_dag.py . C36T --jobs 70 --dynlib ...

The top module `Autocorr.C36T.Gro.Groot` imports the whole closure once (about 4.6 TB of .olean; give the build
machine a small block-device read-ahead, e.g. 64 KB, and enough RAM for ~550 GB resident). Its axiom report
(`results/C36T/axioms_summary.txt`): each of `autocorr_lower`, `autocorr_lower_ess`, `autocorr_lower_real` depends on
propext, Classical.choice, Quot.sound and 2,419,680 native_decide auxiliary axioms (one per job, plus the root box).

## Regenerating the proof of C₁ ≥ 1.32 (`C30`)

The certificate is on Zenodo, doi:10.5281/zenodo.23523705 (78 parts).

    cat c30_132m_cert.tar.part* > c30_132m_cert.tar
    sha256sum c30_132m_cert.tar        # 0aa4923334b4c089a7be957bc6297db4cd30d9f45b67a43fafb987eb0381d761
    mkdir cert30 && tar xf c30_132m_cert.tar -C cert30
    python3 tools/cert_manifest.py cert30
        # files 290309  manifest_sha256 e805206b842db705dbc40bbd79e23857761d48c1e145da401c81c8ea4db77e07
    tools/run_m3x.sh cert30 C30 30 33 25 370

`run_m3x.sh` does the following:

1. builds the checker libraries, with the checker compiled to native code;
2. exports the 290,308 job logs into 67,740 group modules (`Autocorr/C30/`);
3. builds them with `tools/build_dag.py`, then `Main` and `Forms`;
4. writes the `#print axioms` output to `results/C30/axioms.txt`.

On a 384-thread server with 370 workers, the export took 3.4 minutes and the build about 24 minutes, which is
about 136 CPU-hours. The generated sources take about 101 GB. The compiled files take about as much again: the c28
run had 217 GB of source and 219 GB of compiled files. Main imports all modules (about 23 GB resident).

## Other certificates

* `c20_128` is also on Zenodo (`c20_128_cert.tar`, sha256
  10d9a6d89b0dc082babb221859a2593f48762aaa91a1b4af0ad8cbf6eb3a492c).
  - `tools/run_m3.sh cert20 C20 20 32 25 W` builds the `native_decide` proof in minutes.
  - `tools/run_m4.sh cert20 KC20 20 32 25 W` builds the kernel-only proof: 2.9 CPU-hours, or 16 minutes on a
    384-thread server.
* `c28_131` (λ = 131/100) is not archived publicly (81 GB); rerunning these proofs requires its job logs.
  - **Kernel-only:** `tools/run_m4.sh cert28 KC28 28 131 100 W` took 1,561 CPU-hours for the 43,140 check
    modules, at about 3 GB of memory per worker. On machines with less memory per thread, set
    `MIN_AVAIL_GB`/`KILL_AVAIL_GB` for memory-aware scheduling. We split the check modules between two 384-thread
    servers with `tools/build_dag.py --exclude` and joined the results for the assembly.
  - **`native_decide`:** `tools/run_m3.sh cert28 C28 28 131 100 W` took 61 CPU-hours.
* `c24_130` (λ = 13/10) is not archived publicly either.

`results/<package>/summary.txt` records two fingerprints of the files each exporter read:

* the `tools/cert_manifest.py` fingerprint of `meta.json` and the job logs;
* the SHA-256 of the published archive, where there is one.

## How the generated modules work

* **Exporters (untrusted).** The exporters replay every job of the certificate and encode it as Lean data.
  - **`native_decide`:** one module per group of jobs. Each job is a theorem `checkJobStr … = true :=
    by native_decide`, and the jobs are composed by the inductive `Covered`.
  - **Kernel:** each job is cut into segments of at most 4 leaves. Each segment is a theorem
    `segCheck … = true := by decide +kernel`. Every group has a check module, which imports only the constants of
    n, and an assembly module, which composes the segments and the delegated subtrees through `StkK`. The root
    box is the kernel's own interval propagation of `[0, 1]^nB`.
  - The kernel exporter rounds the dual multipliers to multiples of 2^−64 and re-checks every leaf bound exactly
    in integer arithmetic before writing it.
* **`tools/build_dag.py`.** Builds the generated modules outside Lake in dependency order:
  - make-like (only stale modules are rebuilt);
  - bounded parallelism;
  - optional memory-aware start and kill thresholds;
  - `--exclude` for splitting a build across machines.
