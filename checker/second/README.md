# Second checker for the branch-and-bound certificates

This directory holds a second checker for the branch-and-bound certificates of the window bound V_n >= lam: the
tree-only certificates and the logs of the n = 39 search, whose leaves are mostly D records. It was written from the
specification (CERT_FORMAT.md, sections 1-8, and TREE_FORMAT.md) and the mathematics of the paper, separately from the
first checker: without copying from it or from the search program; every accepted bound is evaluated in exact rational
arithmetic. Its author had reviewed the first checker's code beforehand, so it is not claimed to be independently
authored, and a few short lines coincide.

It differs from the first checker in:
- its exact arithmetic: rational numbers, with duals rounded to multiples of 2^-50, instead of integer arithmetic with
  duals at 2^-64 and cut duals at 2^-128;
- its linear-programming code and row management;
- an exact Farkas test for infeasible leaf programs;
- its separate implementation of the structure, region and partition checks, including a structure pass before any
  linear programming;
- a combine step that binds every job file by sha256.

## What it checks

The claim (CERT_FORMAT.md, section 1): for every p in the simplex Delta_n with sum_i (2i-(n-1)) p_i <= 0,

    F(p) = max_{c1<=c2} 2n/(c2-c1+2) sum_{c1<=i+j<=c2} p_i p_j >= lam.

Reversal symmetry covers the other half-space.

**Trusted part.** This part is exact; no floating-point number enters a decision.
- Every row key in meta.json is validated strictly. Rows and square inequalities are built from their definitions.
- Regions are exact rationals, with the interval propagation of section 3.
- Each job's record stream is checked: I, S, K, D, U, T, L and F records, with a stack that must end empty. C and E
  records are rejected.
- The header line of a job log is parsed with Python's json module, which accepts the token Infinity. The checker uses
  only n (equal to that of meta.json), lam (equal to that of meta.json) and path (the root region, rebuilt by exact
  splits, which must be non-empty), and it ignores every other header key; in the n = 39 logs these are the writer's
  statistics, such as "minlb": Infinity in jobs without leaves. meta.json and every record line are parsed strictly
  (NaN and Infinity are rejected).
- The partition across jobs is checked (section 7): unique root paths, every delegated region is exactly one job's
  root, and every job is reachable from the root job.
- A U or T leaf is accepted only if an exact Neumaier-Shcherbina bound LB(y) >= lam holds for some dual vector y.
  - y ranges over the rows of meta.json and square inequalities of the checker's own choosing.
  - Each dual is rounded to a multiple of 2^-50; for a square inequality it is then divided by that inequality's
    integer scale.
  - LB(y) is evaluated in Python's fractions module.
- An infeasible leaf linear program is accepted only through an exact Farkas test.
- An L or F leaf, which carries stored duals, is accepted if its stored dual passes the same exact test. Otherwise the
  checker searches for its own dual, as for a U leaf.
- A D record (the 5- and 6-field forms of CERT_FORMAT.md section 5 that search/bnbtree39f.py writes) is accepted if the
  exact bound of its stored duals, after the completion of the G, P and ZA duals of CERT_FORMAT.md section 6, reaches
  lam. Otherwise the checker searches for its own dual, as for a U leaf.

**Untrusted part.** The oracle only proposes duals, rays and cuts.
- It uses the HiGHS dual simplex through highspy, one thread per worker.
- Window rows, McCormick rows and square inequalities enter the linear program only while they are useful.
- The search stops early once the dual objective passes lam + 1e-6.
- Square inequalities come from the most negative eigenvectors of 3x3 moment matrices of block pairs, with
  coefficients rounded at 2^-20.
- Every setting is fixed in the code; there are no environment switches.

A weak search can only reject a valid certificate, never accept an invalid one.

## Files

| file | contents |
|---|---|
| iv_core.py | exact core: block tree, rows, square inequalities, regions, the exact bound, the completion of D records |
| iv_lp.py | untrusted oracle: HiGHS linear programs and cut separation |
| iv_verify.py | driver: records, leaves, partition, worker pool, split runs and combine |
| test_core.py | unit tests: numbering, row validity at true points, exact bound against the LP value |
| mk_tamper.py, run_tamper.sh | 13 tampered copies of a certificate, each of which must be rejected |
| SAMPLED_VERIFICATION.md | an optional sampled mode, not used for the results below |
| SHA256SUMS | sha256 of every file here |

The run on n = 39 used a copy whose three program files have the combined sha256
31f142a1cdb69b9bfbc8a2cdea06ff238e6e724aa7efe1b96d815d8574b416c4. The files here differ from that copy only in
docstrings: comparing the parsed code with docstrings removed shows no difference. The runs on n = 36 and on the smaller
certificates used an earlier copy (combined sha256 32ba4cc011f0851f339e0e16676b298e18d45263aff4ff44b2d06031d7ae46b2)
that rejected D records and parsed headers strictly. The changes since are the D-record path, the header rule, and
options for cross-checks by the checker's own linear programs and for writing the leaf margins. --combine binds shard
outputs to the hash of the running files, so outputs made by one copy must be combined by the same copy.

## Requirements

Python 3.12, numpy and highspy. Tested with Python 3.12.13, numpy 2.5.4 and highspy 1.15.1.

## Running

On one machine:

    python3 -I iv_verify.py CERTDIR --workers K

CERTDIR holds meta.json and jobs/*.jsonl.gz.

Split over several servers:

    python3 -I iv_verify.py CERTDIR --workers K --shard I/S --out shard_I.jsonl    # on each server, I = 0..S-1
    python3 -I iv_verify.py CERTDIR --combine shard_*.jsonl                        # on one machine with all job files

A shard run checks its own jobs and prints "SHARD I/S OK". --combine accepts the shard outputs only if all of the
following hold:
- they were written by these exact files, so the sha256 of iv_core.py, iv_lp.py and iv_verify.py must match;
- they were written for this meta.json;
- they cover every job file exactly once, with unchanged sha256;
- they contain no failure;
- the partition closes.

Any set of outputs that covers the job files exactly once is accepted. For the n = 36 certificate, batches of job
files were verified while the search was still running: each batch was a directory with meta.json and some of the job
files, run with --shard 0/1 --out. The combine over all batch outputs, run against the final certificate, is the
acceptance.

## Reading the verdict

The certificate is verified only if the program exits with status 0 and its last line starts with "VERIFIED:", for
example `VERIFIED: V_36 >= 133/100 (1.33); jobs=...`. Anything else is a failure: "NOT VERIFIED: ..." with exit status
1, an exception, or an interrupted run. A sampled run prints "SAMPLED-OK (not a full check)" and is never a
verification.

## Tests

    python3 -I test_core.py CERTDIR          # unit tests
    python3 -I mk_tamper.py CERTDIR OUTDIR    # 13 tampered variants
    ./run_tamper.sh OUTDIR K                  # every variant must be reported as REJECTED

The 13 variants are:
- a dropped leaf, a dropped last record and an extra record;
- a delegated region moved by 2^-30;
- a split value moved outside its interval, and the root split moved inside it;
- lam raised in meta.json only, and lam raised everywhere;
- the half-space row removed, and the half-space row malformed;
- a dropped job file, a duplicated job file, and a leaf replaced by a delegation.

## Results

**n = 36, lam = 133/100.**
- 2,419,679 job files: the 2,419,677 written by the search plus 2 regenerated jobs that replace two job files left
  empty on disk.
- 177,077,986 leaves, all accepted; 0 failures.
- One leaf is an L record and was accepted from its stored dual. No leaf needed the Farkas test.
- The smallest exact leaf bound is 1.330000000000692.
- The partition closes: 2,419,678 delegations, each matching exactly one job root.
- Cost: about 42,000 CPU-hours, on up to 297 servers with 32,096 threads in total.
- Combine on the final certificate: `VERIFIED: V_36 >= 133/100 (1.33); jobs=2419679 (combined from 2730 shard outputs)`, exit status 0.

**n = 39, lam = 267/200, on the logs of the search.**
- 13,678,676 job files, read in place on the 487 servers of the search. On every server the set of files that the
  checker read, with their sha256, equals the run's manifest of the job files, and meta.json has sha256
  4b330edc10a01525bfdc5ad0320a253cecff5a89f5546ca951218e4321ef9be4.
- 527,163,006 leaves, all accepted: 526,747,638 D records by their stored duals after completion, the 2 L records by
  their stored duals, and the 415,366 U leaves by duals that the checker found. No D record needed its own search.
- The smallest exact leaf bound is 1.3350000004027083.
- Cost: about 15,300 worker-hours (wall time times workers), on 487 servers with 65,908 threads and 32,954 worker
  processes.
- The per-server outputs were combined on one machine by a separate script, which is not part of this directory; the job
  files never left the servers. The combined verdict is VERIFIED for V_39 >= 267/200 with 13,678,676 jobs and
  527,163,006 leaves.
- The tree-only copy that search/d2tree.py wrote on each server, from which the archived certificate is cut, equals
  these logs with the K records dropped and every D record replaced by U, and everything else byte-identical (checked on
  all 13,678,676 jobs by a separate script, which is not part of this directory). This run did not solve the U leaves of
  that copy again.
- As a cross-check, which acceptance does not need, the checker's own linear programs also certified a random 2% of the
  leaves with stored duals (10,534,695 leaves) and the 527,870 leaves with the smallest stored margins.

**Tests with the files here.** test_core.py: exit status 0 (83,967 row evaluations, 0 violations; the exact bound equals
the LP value). A 41-job n = 16 test certificate (V_16 >= 5/4, 1,977 leaves): VERIFIED both as a tree-only certificate
and as D logs. mk_tamper.py with run_tamper.sh: 13 of 13 variants REJECTED.

**Smaller certificates, with the earlier copy:**
- n = 16: V_16 >= 5/4, 2,158 leaves.
- n = 20: V_20 >= 32/25, 34,239 leaves.
- n = 24: V_24 >= 13/10, 705,473 leaves.
- n = 28: V_28 >= 131/100, 2,669,845 leaves.
- Each of these printed VERIFIED, and every tampered variant of the n = 16 and n = 24 certificates was rejected.
