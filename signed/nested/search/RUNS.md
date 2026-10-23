# Search programs for the tau = 1/4 nested certificate (C' >= 4/3): runs and settings

These are the programs that produced the certificate (the 2,048 parts of one_sided_tau1_4), in the versions that ran. Only
comments, docstrings and path strings were changed. RELEASE_TABLE.tsv lists every file with its source sha256, its release
sha256 and the change. AST_CHECKS.txt shows that each .py has the AST of its source, apart from the docstrings and path
strings it names. Nothing here is needed to check the certificate; the checkers are separate.

## Environment
Python 3.12 with numpy 2.5.4, scipy 1.18.1, highspy 1.15.1 and python-flint 0.9.0 (pinned at install). Every run used
`python -I` with OMP_NUM_THREADS, OPENBLAS_NUM_THREADS, MKL_NUM_THREADS and RAYON_NUM_THREADS set to 1.

## Pipeline
The problem data are tau = 1/4, T1 = (21/20, 3/5, 3/5) and the arcs [k/4096, (k+1)/4096] of [0, 1].
cfg25t.json is cfg25.json plus the tile T7b = (6.4396, -0.0488, 0.4657, 1.1037). In both, "out" and "arcs_file" are not read
by these programs.

1. Coarse E pass (phaseA/): `python -I coarseE.py`.
   - For each of the 512 coarse arcs it tries an E certificate (gen_two_level.solve_E) and records the result in
     coarseE.jsonl.
   - The 8 fine arcs under each coarse arc without one go to fine_arcs.json: 234 coarse E arcs, 2,224 fine arcs.
2. Phase A (phaseA/): 20 shards; shard i is fine_arcs[i::20], written as A25_arcs.json. Each shard ran on its own VM with 96
   processes:
   `NDIR=64 TAU=1/4 D_TASK=0.05 MAXNEST=2 python -I gen_nested3.py A cfg25.json A25_arcs.json 96 A25_out.jsonl`
   - The 20 outputs (A/A_00.jsonl to A/A_19.jsonl) hold the closed arcs and the stubs. A stub is a root whose hard arcs are
     left as phase-B tasks.
   - The phase-A modules are in phaseA/: gen_nested3 2eabb6b5, gen_nested2 5e5a2bfe, check_nested 6dc43c7e, nest3 89e2246e,
     nest_proto aea46a3c, nest2 fad8ce72, gen_two_level f6ab4a72, hslp b77fcf75 (source sha256 prefixes).
3. Task list (phaseA/): `python -I mk_tasks.py T/tasks 20 A/A_00.jsonl ... A/A_19.jsonl`.
   - It writes T/tasks_000.jsonl to T/tasks_019.jsonl: 118,684 tasks, shuffled with seed 12345. Replaying this rule on the
     phase-A outputs gives the same 20 files.
   - phaseB_V22/tasks_up_t25.jsonl holds the 59,342 tasks with k < 2048, in the same order. This is the upper half; the lower
     half of the certificate is the exact mirror image, made at assembly.
4. Phase B, V22 (phaseB_V22/): one claim server and queue workers on spot VMs.
   - Server: `SPLIT=1 python -I qserver.py PORT tasks_up_t25.jsonl done_keys.txt claims.log`
   - Worker: `NDIR=64 TAU=1/4 MAXNEST=2 HREUSE=1 SHORTRAT=2 DEN_BITS=30 W1_N0=16 NEST_RUN=8 CNCACHE=1 LPVEC=1 KVCACHE=1
     KC_MAX=200000 DMAX=0.2 python -I qworker.py http://SERVER:PORT NAME cfg25t.json NPROC OUT.jsonl`
   - Variables left unset, so the code defaults applied: NODE_BUDGET (20000 nodes per task piece in gen_nested2's search;
     nest2 and nest_proto have their own defaults, 100000 and 400), IVSPLIT_DEPTH 8, IVSPLIT_MIN 1e-6.
   - Each output line is one task piece (k, q0, q1): either an ok record holding its subtree, or a failed record (ok false).
5. Splits (splits/): some band tasks hit the node budget or stalled (T3d tiles, q about 0.816-0.831). Each was split into 16
   equal q-pieces, q0 + (q1 - q0) i/16 (Fraction strings), and the pieces ran on the same workers from a second server.
   - split1: 311 parents, 4,976 pieces. It was made by a one-off command with the same rule as split2_make.py.
   - split2: 26 parents, 416 pieces (split2_make.py).
   - split1_manifest_check.py and split2_manifest_check.py check each manifest with the assembler's chain rule
     (stream_assemble.py, lines 59-78): PASS.
6. Phase B, V23 (phaseB_V23/): its programs differ from phaseB_V22/ only in gen_nested2.py (42d05a46 against 1a57ec59).
   - From 2026-10-23 02:40Z the 2,927 unfinished pieces ran with the V22 switches plus IV_SKIPREP=2: at nodes inside an
     ivsplit subtree, the search skips make_rep2 and the 3 tau_rep retries (V22 does not read IV_SKIPREP).
   - 91 pieces hit the node budget. They were split again by split3_make.py into 1,456 pieces, which all finished ok.
     split3_manifest.jsonl passes the same check.
7. Assembly (assembly/, NS = 2048): assemble2_t25.sh runs two commands.
   - `python -I mirror2.py 'prod25A/A/A_*.jsonl' 'B/*.jsonl' A_sym.jsonl B_sym.jsonl` makes the lower half as the exact
     mirror of the upper half.
   - `python -I stream_assemble.py cfg25t.json 1/4 prod25A/coarseE.jsonl A_sym.jsonl B_sym.jsonl asm_work cert_t25.json.gz 2048 cert_t25_sub`
     writes the certificate and its 2,048 parts.
   - Inputs: the phase-A data in prod25A/ (coarseE.jsonl and A/A_*.jsonl) and all worker outputs in B/. Neither is part of
     this release.
   - A task piece is taken from its own ok record, or else from the exact chain of ok sub-pieces. Failed records never enter
     the certificate.
   - The script first checks the production bundle's BUNDLE_SHA256SUMS. With these release files, run the two commands
     directly.
