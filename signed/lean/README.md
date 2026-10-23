# Lean 4 proof of C₃ ≥ C₃′ ≥ 30/23

This directory holds a Lean 4 + Mathlib proof of the weaker bound C₃ ≥ C₃′ ≥ 30/23 for the signed third autocorrelation
constants, from the certificate `one_sided_tau7_30.json.gz` with τ = 7/30 (sha256
1a530af38c24b53f9bd5b0b183964d871eacce999e64f0487655b04342b94f18, in the Zenodo record). Theorem 1.3 of the paper states
4/3 and has no Lean proof; the bound 25/19 of Section 6 of the paper has the Lean proofs in `../lean_25_19` and
`../lean_kernel_25_19`. Docstrings in `src/` use another numbering: their Theorem 6.1 (`C64/Defs.lean`,
`C64Data/Main.lean`) is Theorem 1.3 of the paper with 30/23 in place of 4/3, their Lemma 6.3 is Lemma 6.2, their
Lemma 6.4 is Lemma 6.3 and their Lemma 6.6 is Lemma 6.4; Lemma 6.5, Definition 6.6, Proposition 6.7 and Corollary 6.8
agree.

The bound C₃ ≥ C₃′ ≥ 30/23 is verified in Lean 4 with Mathlib; the 2,627 finite certificate checks are evaluated by
native_decide (one auxiliary axiom per check), and the exported proof, with the auxiliary axioms taken as given, is
accepted by `leanchecker` and by two other kernel implementations, nanoda and lean4lean.

## Statements (`src/C64/Defs.lean`)

* `C64Data.mainStatement : C64.MainStatement`. For every `f : ℝ → ℝ` that is integrable and zero almost everywhere
  outside `[−1/4, 1/4]`, with `∫ f ≠ 0`, every real number `M` with `(f ⋆ f)(t) ≤ M` for almost every `t` satisfies
  `(30/23) (∫ f)² < M`.
* `C64Data.mainStatementEss : C64.MainStatementEss`. For the same `f`, with essential suprema in `EReal`:
  `(30/23) (∫ f)² < ess sup (f ⋆ f) ≤ ess sup |f ⋆ f|`.
* `C64Data.constStatement : C64.ConstStatement`. `30/23 ≤ C₃′ ≤ C₃`, where `C₃′` (and `C₃`) is the supremum in `EReal`
  of the constants `C` such that every admissible `f` and every real almost-everywhere upper bound `M` of `f ⋆ f` (of
  `|f ⋆ f|`) satisfy `C (∫ f)² ≤ M`.

Here `f ⋆ f` is Mathlib's convolution with respect to Lebesgue measure. The theorems have no further hypotheses.

## How the proof works

* `src/C64/` formalizes the argument of Section 6 of the paper in winding-number form, without the argument principle or
  the Jordan curve theorem, and proves the checker sound. It uses only the three standard axioms.
* `src/C64Core/` is the checker (core Lean only, compiled to native code): it re-derives every condition of the
  certificate from the definitions, with exact arithmetic and interval enclosures.
* `src/tools/` translates the certificate into Lean data: `C64Data/Glob.lean` with the global data and one module
  `C64Data/A<i>.lean` for each of the 2,626 intervals of `T1`. Each arc module proves `checkArc C64Data.glob A<i>.arc =
  true` by `native_decide`: for an interval of type E the exclusion along the arc, for one of type H the crossing
  localization and every leaf of its tree. `Glob.lean` proves `checkGlob glob = true`: the parameters and the odd
  winding number of `S` along `T1`. `C64Data/Main.lean` assembles these into the three theorems. The statements do not
  mention the certificate, so the exporter need not be trusted.

## Axioms

Each of the three theorems depends on `propext`, `Classical.choice`, `Quot.sound` and 2,627 `native_decide` auxiliary
axioms, one per interval of `T1` and one for the global checks. `native_decide` makes the Lean compiler part of the
trusted base. `axioms_clean.txt` is the output of `Axioms.lean` (`#print axioms` for the three theorems).

## Versions and hashes

* Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `v4.35.0-rc3` (commit c55e6e786f49; `src/lake-manifest.json`).
* `source_sha256.txt`: the sha256 of every source file in `src/`.
* `data_sha256.txt`: the sha256 of the concatenation of the generated modules `C64Data/A*.lean` in sorted order,
  30145faff4cbcfaccf87d722dc668ef39de8fe3b9bda228af8deb8c809056182. The 2,626 generated modules (1.3 GB) are not in this
  directory; the tools regenerate them from the certificate.

## Building

Requirements: elan (`src/lean-toolchain` pins `leanprover/lean4:v4.35.0-rc3`; Mathlib `v4.35.0-rc3`, commit
c55e6e786f49, in `src/lake-manifest.json`) and Python 3 with `python-flint` 0.9.0, with which the exporter evaluates the
crossing radius of the certificate in ball arithmetic at 80 bits. Run the steps in `src/`, with the certificate
`one_sided_tau7_30.json.gz` from the Zenodo record in that directory.

1. Split the certificate into `SPLIT/glob.json` (variant, τ, `T1`, tiles, number of intervals and the sha256 of the
   input) and `SPLIT/arcs/0000.json` to `2625.json`, sorted by `s0`:

       python3 -I tools/split_cert.py one_sided_tau7_30.json.gz SPLIT

2. Write the Lean data, `C64Data/Glob.lean` and one module `C64Data/A0000.lean` to `A2625.lean` per interval (about 30
   minutes in one process; eight processes with `--range a:b` for `a = 329k`, `b = min(329(k+1), 2626)`, `k = 0..7`,
   give the same output):

       python3 -I tools/gen_lean_data.py SPLIT . --modules

3. Check the data against `data_sha256.txt`:

       ls C64Data/A*.lean | sort | xargs cat | sha256sum    # 30145faff4cbcfaccf87d722dc668ef39de8fe3b9bda228af8deb8c809056182
       sha256sum C64Data/Glob.lean                          # 1b919bb3063769c0c98207bb1378e2bb370e7dd2c118f2dc92263c3a8aae1411

4. Build Mathlib, the checker (compiled to shared libraries under `.lake/build/lib/lean`) and the soundness proof:

       lake exe cache get
       lake build C64Core C64Core.Load C64.Check.SoundMain

5. Build the 2,627 data modules, `JOBS` at a time (logs in `results/shards/<module>.log`, whose last line is `OK ms` or
   `FAIL ms`; the last line of output is the number of failed modules, which must be 0):

       tools/build_shards.sh JOBS

6. Regenerate `C64Data/Main.lean` (sha256 18077f919dd9ad925717004e089503bfd1cbb22299a3df756094ebd3c251e2b8, as
   shipped) and compile it (a few seconds):

       python3 -I tools/gen_main.py 2626 . "7 / 30"
       D=.lake/build/lib/lean
       lake env lean --load-dynlib=$D/LeanC64_C64Core_Ival.so --load-dynlib=$D/LeanC64_C64Core_Num.so \
           --load-dynlib=$D/LeanC64_C64Core_Check.so -o $D/C64Data/Main.olean C64Data/Main.lean

7. Print the axioms and compare them with `axioms_clean.txt`: each of the three theorems depends on `propext`,
   `Classical.choice`, `Quot.sound` and exactly 2,627 `native_decide` auxiliary axioms (`C64Data.globOK` and
   `C64Data.A0000.ok` to `C64Data.A2625.ok`):

       cp ../Axioms.lean . && lake env lean Axioms.lean

Resources: about 18 GB of disk at the peak (`SPLIT` holds 4.7 GB of JSON and can be deleted after step 2; the data
sources take 1.3 GB, their compiled modules 1.6 GB, Mathlib about 7 GB and the toolchain about 3 GB). A data module
needs about 0.2-0.3 GB of memory while it compiles, and `Main.lean` a few GB. The 2,627 data modules took about 133
CPU-hours in total and 77 minutes of wall-clock time on two servers with 140 threads in total; the slowest one took
about 21 minutes.
