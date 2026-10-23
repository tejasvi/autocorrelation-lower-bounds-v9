# kc36: kernel-only Lean proof of C1 ≥ 133/100 (KC36)

This directory is a self-contained Lean package: the library and tools with which KC36 was built, unchanged, plus
the KC36 build steps (`scripts/`) and results (`results/KC36/`). Its kernel checker differs from the one in `../`
(which built KC20 and KC28) in two ways: it checks the certificate's square cuts as cut records
(`AutocorrK/Core.lean`, `Autocorr/KSound/Cut.lean`, `tools/kc_ref.py`), and its block-descriptor fields are 13 bits wide
instead of 12 (`AutocorrK/Core.lean`, `AutocorrK/Table.lean`, `tools/kc_export.py`), as n = 36 needs.

Package KC36: λ = 133/100, certificate c36t (n = 36), checked by the kernel; all three theorems; axioms at most propext,
Classical.choice and Quot.sound (from the module scan described below; `#print axioms` was not run).

Every segment of every job's DFS log is a `decide +kernel` check of `AutocorrK.segCheck`, composed by
`AutocorrK.StkK`; there is no `native_decide` anywhere in the package.

## Building from the filled certificate

The input is the filled c36t certificate: the job logs of the archived certificate `c36t_V36_133_certificate.tar`, with
every tree-only leaf replaced by an explicit leaf that carries the dual the exact check accepted. It has 2,419,679 job
files and 177,077,986 leaves, about 2.1 TB, and is not archived. To make one, run `../../checker/verify_tree_dump.py` on
the archived certificate with `VT_DUMP_DIR` set: it writes every job, with its accepted tree-only leaves filled, into that
directory. Compare the files with `c36t_filled_certificate.sha256.gz`, a separate file of the record (sha256, size and
name of each file). Only inputs identical to that list reproduce the hashes in `kc36_oleans.sha256.gz`; another filled
certificate gives the same three theorems if it passes the export's exact re-check and the build.

1. `lake build` in this directory (Lean v4.35.0-rc3, Mathlib c55e6e786f49; `lake-manifest.json`).
2. Shards: `results/KC36/partition.json.gz` lists the 620 jobs at the top of the tree and the roots of the 6,372
   subtrees below them, in 202 shards. For each shard, put the filled job files of its subtrees (with meta.json) in a
   directory and run `scripts/shard_build.sh DIR JOBS LOG`. That is `tools/kc_shard.py --group-leaves 1000 --seg-leaves 1`;
   its first pass re-checks every leaf exactly with the rounded duals. Then `tools/build_dag.py` builds the modules.
   Every shard also builds the shared module `Autocorr.KC36.Params`.
3. Top: with all shard modules in `.lake/build/lib/lean`, run `scripts/top_export.sh TOPDIR KEXT JOBS`. TOPDIR holds the
   620 top job files, and KEXT is `results/KC36/kext.json.gz` uncompressed: the shards' subtree roots, reached as
   external modules. Then run `scripts/top_build.sh JOBS SCANDIR`: it builds `Params` and the 78 check modules, then the
   top module `Autocorr.KC36.Gro.Groot`, then the axiom scans.

Layout note: `tools/merge_top.py` moves the bodies of the generated `Main.lean` and `Forms.lean` into the top module.
That module therefore proves the three theorems, with unchanged statements; `results/KC36/top_module_bound.lean` is that
part of it, verbatim from the built module. `results/KC36/Main.lean` and `Forms.lean` were reconstructed after the
build: `Main.lean` from the template in `tools/kc_shard.py`, `Forms.lean` by running `tools/forms.py KC36 36 133 100`.
They were checked against the built top module: combined by `tools/merge_top.py`'s rule, they reproduce its theorem part
and its import header byte for byte. The independent audit did not check this reconstruction.

## Figures

- Modules: 2,274,566 in total.
  - 2,274,486 shard modules in 202 shards (counts per shard: `results/KC36/build_shards.tsv`).
  - For the 620 top jobs: `Params`, 78 check modules and the top module (151,677 leaves, 152,297 segments).
- CPU time, shards: about 58,500 CPU-hours to build the shard modules. This is an estimate from shard 333, which was
  rebuilt on the assembly server (11,467 modules with `Params`, 881,444 leaves): 291.6 CPU-hours, the sum of the user CPU
  time of each module's `lean` process as `tools/build_dag.py` records it (system time not included), 1.19 CPU-seconds
  per leaf. Measured in the audit's independent rebuild: 53,858 CPU-hours of Lean user time for 200 of the 202 shards,
  including 11,127 module builds that were repeated after interruptions. The export was not timed separately for every
  shard; on shard 333 it took 3 minutes of wall time with 200 workers for 12,026 jobs, so at most about 10 CPU-hours.
- CPU time, top:
  - export: 45 minutes of wall time with 16 workers (202.5 s exact re-check of the 620 jobs, 2,522.6 s writing);
  - `Params` and the 78 check modules: 33.0 CPU-hours;
  - top module: 0.6 CPU-hours (866 s user, 1,305 s system).
- Wall-clock time: about 4.7 hours for the 202 shards, built in parallel, including the transfer of the compiled modules
  to the assembly server. On that server: `Params` and the 78 check modules (36 minutes, in one build together with the
  last 1,732 modules of shard 333), the top module (49 min 49 s) and the module scan (5 minutes).
- Servers: 202 servers with 60 to 384 hardware threads for the shards; one server with 224 hardware threads and 2.9 TiB
  of memory for the top.
- Memory: at most 16.3 GB resident per shard or check module (median 2.1 GB). The top module imports all other modules:
  2.6 TiB resident, after a targeted page prefetch of every compiled module (`../tools/prefetch_olean.py`, read-ahead off).
- Duals: row duals are rounded to multiples of 2^-64, as for KC20 and KC28; the window rows are rescaled first. Square-cut
  duals are floored to multiples of 2^-94 and are nonnegative. The export re-checks every leaf exactly with these rounded
  duals.
- Axioms: `#print axioms` was not run, for two reasons: it needs one process that imports every module, and the top module
  was compiled without the in-module axiom report. `tools/kscan.lean` read all 2,274,566 compiled modules: no axiom is
  declared in the package and no constant refers to `sorryAx` or to native evaluation. `tools/kscan_ext.lean` showed that
  the 120 constants outside the package that a package constant names in its type or value depend only on propext,
  Classical.choice and Quot.sound. An independent scan with separate code found 228 external references, with the same
  three axioms (`results/KC36/axioms.txt`).

## Comparing a rebuild with the published hashes

`kc36_oleans.sha256.gz` (a separate file of the record) lists the sha256 of every compiled KC36 module: 2,274,566 lines,
sorted by path. Each line is `sha256  Autocorr/KC36/[<dir>/]<module>.olean`: the hash of the `.olean` file alone, with
the path relative to `.lake/build/lib/lean`. To compare:

    cd .lake/build/lib/lean
    zcat /path/to/kc36_oleans.sha256.gz | sha256sum -c --quiet                   # a complete build: prints mismatches only
    zcat /path/to/kc36_oleans.sha256.gz | sha256sum -c --quiet --ignore-missing  # a partial build, e.g. one shard

An independent rebuild from the same inputs reproduced every shard module, `Params` and the 78 check modules byte for
byte against this list. The top module, which imports everything, was replayed by the Lean kernel.
