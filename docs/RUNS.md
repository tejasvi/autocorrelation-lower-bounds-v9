# Notes on the runs reported in the paper

These notes record settings and incidents of the runs that the paper reports. None of them can make a checker accept a
leaf whose exact bound is below lam.

## The certificate of V_39 >= 267/200

- **Node budget of the search.** The budget only decides where jobs are cut. It was one node during a fan-out of
  three minutes at the start of the search, then, after about five minutes with the values 125, 31 and 200, mostly 500
  (200 on servers that joined later), and 100 and then 20 near the end.
- **Solver setting, first checker on the logs of the search.** For the 46,627 jobs on two of the servers where the
  linear program of a leaf without data had stalled, the first checker ran HiGHS with a limit of 100,000 simplex
  iterations (`VT_HIGHS_OPTS='{"simplex_iteration_limit": 100000}'`); this limit affects only the search for a dual
  vector.
- **Solver setting, first checker on the archived certificate.** That run used the same limit of 100,000 simplex
  iterations for every job.
- **Lean fill.** The dump verifier that filled the leaves without data for the Lean proof ran two of its jobs with
  `VT_HIGHS_OPTS='{"simplex_strategy": 4}'`, an option of the solver that searches for a dual vector.
- **Archived copies.** During the run of the first checker on the tree-only copies of the logs, the copies on the
  servers were read-only. Their SHA-256 hashes, recorded during the run and again after it, agree with each other and
  with those of the archive, and the results of the run cover exactly these files. The jobs of one server were checked
  on four other servers, and the copies there, hashed after their runs, gave the same hashes.
- **Second checker on the logs of the search.** It read the logs in place on the 487 servers of the search, with 32,954
  worker processes; on every server the set of job files that it read, with their SHA-256 hashes, equals the manifest of
  the run, and a separate script combined its per-server results. As a cross-check, its own linear programs also
  certified a random 2% of the leaves with stored dual vectors and the 0.1% of them with the smallest stored margins.

## The certificate of V_36 >= 133/100

- **Solver setting.** In 37 of the 791 parts of the run of the first checker, HiGHS with its default options stalled;
  for their 298,364 jobs, listed in `ORACLE_OPTS.txt` of the archive, the checker used the same limit of 100,000
  simplex iterations.
- **Regenerated job logs.** Two job logs that a server interruption had left empty were generated again over the same
  regions (`REPAIR.md` in the archive).
- **Lean check.** The 490,501 modules were generated and compiled on 202 servers in about 2,200 CPU-hours; the top
  module took about 20 minutes on one server.

## The certificate of V_30 >= 33/25

- **Solver revision.** Most of its jobs ran an earlier revision of `bnbopt.py` without the HiGHS iteration limit, which
  was added during the run when eight jobs stalled. The certificate format is the same for both.
- **Duplicate jobs.** After a move between servers, two servers occasionally processed the same job. One job per region
  was kept (`keep.txt` in the archive), and the Python checker confirms that the kept jobs partition the region.

## The nested certificate of C_3 >= C_3' >= 4/3

- **Search.** The second phase worked on 59,342 tasks of the upper half of T1, the hard tile arcs that the first phase
  left, each with a budget of 20,000 nodes. Tasks that exceeded it or stalled were divided into 16 equal pieces, in up
  to two rounds; 333 of the 59,342 tasks enter the certificate as such pieces, which gives 65,702 pieces in all. The
  first version of the second phase wrote 61,410 of them and the second 4,292; the second differs only in skipping,
  inside the subtrees of arc splits, attempts that could not succeed there, and writes the same format. The intervals of
  the lower half are the mirror images of those of the upper half, and an assembly program joined all pieces into the
  certificate file and its 2,048 parts. The coarse pass and the first phase ran with an earlier version of the search
  programs: the coarse pass gave 234 intervals of type E, and the first phase, on the 2,224 finer intervals below the
  others, gave 42 more of type E, closed 590 of type H, and left the hard tile arcs of the remaining 1,592 as the tasks
  of the second phase. All versions, with the commands and settings of every step, are in `signed/nested/search/` (see
  its `RUNS.md`).
- **Checks of record.** `check_nested.py` ran through `check_run2.py`, one part at a time with `--subset --deep`,
  Python 3.12.13, python-flint 0.9.0, NPROC = 7 and one thread per process. Two servers with 384 threads ran 40 to 48
  such runs at a time, under a common memory limit of 360 GiB, and four servers with 96 threads ran 12 each; the checks
  took 3 h 27 min in all, about 2,300 CPU-hours, with at most 8.3 GB of memory per run. Every one of the 2,048 runs
  ended with status 0 and `SUBSET: n of n arcs pass`. `coverage_subsets2.py` then checked the 2,048 hashes, the common
  header and the coverage of [0, 1] (`COVERAGE OK`, 2,458 arcs).
- **Second checker.** `indep_nested.py` ran on the 103 parts of `INDEP_SAMPLE.txt`, each run on one part with `--subset
  --deep`, on four servers with 384 threads, two at a time, with 2, 8, 16 or 32 worker processes per run depending on
  the size of the part: 13 parts in 40 minutes and the other 90 in 59 minutes, 1 h 39 min in all. Every run ended with
  status 0 and the line `SUBSET OK: N arcs pass`, with N equal to the count of the run of record of `check_nested.py`
  for the same part, 121 arcs in all. It used 337 CPU-hours (user and system time), about 3.4 times the 100 worker-hours
  of `check_nested.py` on the same parts; that figure, the elapsed time of the runs of record times their seven
  processes, is an upper bound for their CPU time. The factor was 2.0 to 2.5 on the servers where each worker process
  had about one core, and 4.0 on the server that ran two worker processes per core.
- **Replay.** Before the release, the commands of the README for this certificate were run as written on one server with
  8 threads and 30 GiB of memory (Python 3.12.13, python-flint 0.9.0), from a clean copy of `signed/nested/` and the
  archive file, with NPROC = 7 and the loop restricted to parts 228 (the largest), 1413, 1843 and 1970. A swap file of
  32 GiB was added during the run, so that a lack of memory could not end a run of `indep_nested.py`; it was not used,
  and the commands were not changed. The archive check, the extraction and the coverage check of all 2,048 parts passed,
  `check_nested.py` accepted the four parts, and `indep_nested.py` accepted parts 1413, 1843 and 1970. On that server
  `check_nested.py` took 48 minutes on part 228 and 9 minutes on part 1970, and `indep_nested.py` 31 minutes on part
  1970. The run of `indep_nested.py` on part 228 had not finished when this release was frozen.
- **Exit status.** Earlier versions of `check_nested.py` ended with status 0 in the `--subset` mode even when an arc
  failed; the version shipped here ends with status 1, and `check_run2.py` also requires the line
  `SUBSET: n of n arcs pass` with equal numbers.

## The certificate of C_3 >= C_3' >= 25/19

- **Low-memory runner.** `signed/checker/check_three_level_lowmem.py` starts the worker processes of the first checker
  so that they do not copy the parsed certificate, and calls the checker unchanged. The 38 minutes of the first checker
  in the README were measured with this runner; the second checker starts its workers itself.
- **Memory.** In both checkers the main process holds the parsed certificate, about 40 GB, and more while parsing.
  The totals were not measured for this certificate. For the certificate below, each checker needed about twice its
  main process with 360 workers (each worker of the first checker added about 64 MB, and the workers of the second
  checker hold all intervals a second time). The intervals here are about twice as large on average, so expect roughly
  80 GB or more for either checker with a few hundred workers. The chunk files of the second checker take about the
  size of the decompressed JSON on disk.

## The certificate of C_3 >= C_3' >= 30/23

- **Memory.** With 360 worker processes each checker used about 43 GB in total. In both checkers the main process holds
  the parsed certificate, about 20 GB (about 25 GB while parsing); each worker of the first checker adds about 64 MB,
  and the workers of the second checker hold all intervals a second time.
