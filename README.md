# Certified lower bounds for the first and the signed third autocorrelation constants

Programs, checkers, certificates and Lean 4 formalization for the paper *Certified lower bounds for the first and the
signed third autocorrelation constants* by Tejasvi Singh Tomar (Zenodo,
[doi:10.5281/zenodo.23585540](https://doi.org/10.5281/zenodo.23585540)). The certificates are archived with the programs
at [doi:10.5281/zenodo.23585545](https://doi.org/10.5281/zenodo.23585545):

- the certificate of the bound for the first autocorrelation constant (11.0 GB, compressed);
- the nested certificate of the bound for the signed constants, in 2,048 parts collected in one tar file (25.2 GB);
- certificates of the weaker bounds 25/19 (2.7 GB, compressed) and 30/23 (1.3 GB, compressed) for the signed
  constants, which the Lean proofs of these bounds read;
- the certificate of the smaller bound `C₁ ≥ 1.33` (4.8 GB).

## Theorems

**First autocorrelation constant.** For every measurable `f : ℝ → [0, ∞]`,

    sup_{|t| ≤ 1/2} ∫ f(t − x) f(x) dx  ≥  (267/200) · (∫_{−1/4}^{1/4} f)².

So the first autocorrelation constant (Problem 6.2 of Georgiev, Gómez-Serrano, Tao and Wagner,
arXiv:2511.02864) satisfies C₁ ≥ 1.335. The previous best lower bound by other authors was 1.2937 (Kim and Pilanci,
arXiv:2606.31182).

**Signed constants.** For every integrable `f : ℝ → ℝ` that vanishes almost everywhere outside `[−1/4, 1/4]` and has
`∫ f ≠ 0`,

    ess sup |f∗f|  ≥  ess sup f∗f  >  (4/3) · (∫ f)².

So the constants of Problem 6.4 of the same list satisfy C₃ ≥ C₃′ ≥ 4/3 (C₃′: one-sided, `max f∗f`;
C₃: two-sided, `max |f∗f|`). In the repository of optimization constants (github.com/teorth/optimizationproblems),
C₃ is constant 1d, the signed third autocorrelation constant. The trivial lower bound is 1.

## The first autocorrelation constant

### Proof outline

1. **Reduction** (Cloninger and Steinerberger). Let `p_i` be the masses of `f` on `n` equal bins of
   `[−1/4, 1/4]`. Each window of `[−1/2, 1/2]` gives `sup f∗f ≥ q_W(p)`, so `C₁ ≥ V_n`, the minimum over
   the simplex of `max_W q_W(p)`.
2. **Certificate** for `V_39 ≥ 267/200`: a branch-and-bound tree over the masses of the blocks of a balanced binary
   tree of bins, with 13,678,676 jobs (subtrees) and 527,163,006 leaves. The certificate records the tree: the split
   decisions and, for each leaf, a record that the leaf is closed. Two leaves, whose margins in the search were below
   10⁻⁷, also carry their dual vectors and their 35 and 55 square cuts, which the checker reads exactly.
3. **Checking.** `checker/verify_tree.py` needs Python 3 with `numpy`, `scipy` and `highspy`. It rebuilds the
   constraints from their keys and recomputes the regions from the split decisions. For each leaf without data it
   solves a linear relaxation (McCormick inequalities for products of block masses, and its own integer square cuts
   `(v₀ + v_D m_D + v_E m_E)² ≥ 0`) with HiGHS, rounds the dual vector, and accepts the leaf only if the
   Neumaier–Shcherbina bound of that vector, evaluated exactly in integer arithmetic, is at least 267/200. The solver
   is not trusted: a poor dual vector can only make the check fail. Finally the checker confirms that the leaves cover
   the half-simplex. The formats are specified in `docs/CERT_FORMAT.md` and `docs/TREE_FORMAT.md`.

### Checking the certificate

    # download the certificate from Zenodo, then
    sha256sum c39t_V39_1335_certificate.tar.zst    # 645b58d0ca44563331e5b5e438ae0cd7bd5e64f8f2982cd1416c3e3b519fb9ac
    tar --zstd -xf c39t_V39_1335_certificate.tar.zst    # creates the directory c39t (GNU tar 1.31 or later)
    VT_HIGHS_OPTS='{"simplex_iteration_limit": 100000}' \
        python3 -I checker/verify_tree.py c39t --workers NPROC --expect-n 39 --expect-lam 267/200

With an older tar, `zstd -dc c39t_V39_1335_certificate.tar.zst | tar -xf -` unpacks the archive. Here `NPROC` is the
number of worker processes.

The checker relies on assert statements and refuses to run under `python -O`. To read the result, check the exit status
and the final `VERIFIED` line on standard output.

Our run on this certificate used Python 3.12.13, numpy 2.5.4, scipy 1.18.1 and highspy 1.15.1. The whole check takes
roughly 320,000 CPU-hours (about 1.5 to 3 CPU-seconds per leaf, depending on the machine), so it is best split across
machines. Run the checker with `--summary PART.jsonl` on directories that each hold `meta.json` and a subset of `jobs/`.
Then run it with `--combine PART1.jsonl PART2.jsonl ...` and the full directory as the certificate directory. This step
checks that the jobs form a partition of the root region. The combine step trusts the summary files, so a combined
`VERIFIED` counts only for summaries that this checker wrote in the same controlled run.

The reference run set `VT_HIGHS_OPTS='{"simplex_iteration_limit": 100000}'` for all jobs. It bounds the iterations of
the solver that searches for a dual vector; without it, a few leaf programs can run for a long time. With the limit, a
leaf whose linear program does not finish within it fails, so check a job that fails only for this reason again without
the variable. Acceptance rests only on the exact evaluation of the bound, which the variable does not change.

### The second checker

`checker/second/` holds a second checker for tree-only certificates and for the logs of the n = 39 search. It was
written from `docs/CERT_FORMAT.md` (sections 1-8), `docs/TREE_FORMAT.md` and the paper, after a review of the code of
`checker/verify_tree.py`, but without copying from it or from the search programs. It differs from that checker in its
exact arithmetic (Python's `fractions`, with duals rounded to multiples of 2⁻⁵⁰, instead of integers with duals at 2⁻⁶⁴
and 2⁻¹²⁸), in its linear-programming code and row management, in an exact Farkas test for infeasible leaf programs, and
in a pass that checks all records and regions before any linear program. Its partition check follows that of
`verify_tree.py`. It also reads D records, whose stored duals it completes and evaluates exactly. It needs Python 3 with
`numpy` and `highspy` (tested with Python 3.12.13, numpy 2.5.4 and highspy 1.15.1). A split run records the SHA-256 of
every job file, and its combine step accepts the outputs only if they cover every job file of the certificate exactly
once with unchanged SHA-256. `checker/second/README.md` gives the commands and tests.

On the logs of the search for `V_39 ≥ 267/200` it accepted all 527,163,006 leaves: 526,747,638 by their stored dual
vectors after completion, the two leaves with data by theirs and the 415,366 others with duals that it found. A separate
script, not in this repository, combined the per-server results and confirmed the partition; another confirmed that the
tree-only copy of the logs from which the archived certificate is cut has the same tree. That run took about 15,300
worker-hours on 487 servers with 65,908 threads (32,954 worker processes).

On the certificate of `V_36 ≥ 133/100` an earlier copy of it, which did not read D records, accepted all 177,077,986
leaves, and that run took about 42,000 hours of single-threaded workers on up to 297 servers with 32,096 threads in
total.

### Smaller certificates

The same search with `n = 36` gave a certificate of `V_36 ≥ 133/100`, with 2,419,679 jobs and 177,077,986 leaves, one of
them with a stored dual vector and 21 square cuts. It is in the same Zenodo record and also has two Lean proofs, one
through `native_decide` and one checked by the Lean kernel alone (`lean/kc36/`):

    sha256sum c36t_V36_133_certificate.tar    # 92720a0d50750ecb338b45232e53ef3b3859dd086adce111884452d136000a00
    tar xf c36t_V36_133_certificate.tar       # creates the directory c36t
    python3 -I checker/verify_tree.py c36t --workers NPROC --expect-n 36 --expect-lam 133/100

The jobs listed in `c36t/ORACLE_OPTS.txt` verify quickly with `VT_HIGHS_OPTS='{"simplex_iteration_limit": 100000}'`.
With the default settings of the solver they can take hours. Apply the setting only to the listed jobs, since the limit
can make other leaves fail (see above): put them in a directory of their own, run `--summary` there with the variable
set, and run the other jobs without it.

`c36t/REPAIR.md` lists the two job logs that were generated again after a server interruption, with their old and new
SHA-256 (`docs/RUNS.md`).

`checker/verify_tree_dump.py` is the same checker, with the acceptance logic of `verify_tree.py`, plus one extra
output: when `VT_DUMP_DIR` is set, it writes the accepted dual vector of every leaf as a certificate with stored
duals, which the Lean exporter reads. Copies of both checkers, identical byte for byte, are in the archive of `V_36` as
`verify_tree_bae09172.py` and `verify_tree_dump_34da7947.py`.

`checker/verify_cmp.py` checks format 2, in which every leaf stores its dual vector (for most leaves in compressed
form). In this format we certified `V_30 ≥ 33/25`, with 290,308 jobs and 24,935,952 leaves. The certificate is archived
in 78 parts at [doi:10.5281/zenodo.23523705](https://doi.org/10.5281/zenodo.23523705):

    cat c30_132m_cert.tar.part* > c30_132m_cert.tar
    sha256sum c30_132m_cert.tar    # 0aa4923334b4c089a7be957bc6297db4cd30d9f45b67a43fafb987eb0381d761
    mkdir cert && tar xf c30_132m_cert.tar -C cert
    python3 -I checker/verify_cmp.py cert --workers NPROC --expect-n 30 --expect-lam 33/25

With `NPROC = 375` on a 384-thread server this check took 39 minutes, and the time scales inversely with `NPROC`.

`checker/verify.py` checks format 1, which has no square cuts or compressed leaves. In format 1 we also certified
`V_20 ≥ 32/25`, `V_24 ≥ 13/10` and `V_28 ≥ 131/100`. The certificate of `V_20 ≥ 32/25`
(`c20_128_cert.tar`, 321 MB) is in the same Zenodo record. It checks in about 80 seconds with 32 workers:

    mkdir c20 && tar xf c20_128_cert.tar -C c20
    python3 -I checker/verify.py c20 --workers 32 --expect-n 20 --expect-lam 32/25

### Lean formalization

`lean/` holds proofs of `C₁ ≥ 1.335` and `C₁ ≥ 1.31` in Lean 4 with Mathlib, from the certificates of `V_39 ≥ 267/200`
and `V_28 ≥ 131/100`, and a Lean proof through `native_decide` from the certificate of `V_36 ≥ 133/100`. The reduction,
the reversal symmetry and the soundness of a certificate checker are proved there, and the Lean checker re-implements
the constraints and proves them valid. An exporter translates the job logs into Lean source; for the leaves without dual
vectors it takes those that `checker/verify_tree_dump.py` writes for the leaves it accepts. The theorem statement does
not mention the certificate, so the exporter need not be trusted. The Lean checker runs through `native_decide`, which
makes Lean's compiler part of the trusted base: the theorem for 267/200 depends on the three standard axioms and on
13,678,677 axioms that record compiled evaluations, one per job and one for the root region (2,419,680 for the theorem
for 133/100). For `V_39 ≥ 267/200` the logs of the search carry dual vectors for most leaves. The frozen dump verifier
(sha256 34da7947...) filled the 385,629 job files that contain leaves without data, and the Lean proof reads these files
and the other logs unchanged. The list of all 13,678,676 files (SHA-256, size, name) is
`c39t_filled_certificate.sha256.gz` in the Zenodo record.

The Lean checker accepts the certificate of `V_30 ≥ 33/25` as well. The formalization also gives the statement with the
essential supremum, and a version for real-valued `f` stated with Mathlib's convolution.

Another checker runs in the Lean kernel alone. It proves `V_28 ≥ 131/100`, and hence `C₁ ≥ 1.31`, from the three
standard axioms only, and it also accepts the certificate of `V_20 ≥ 32/25`. See `lean/README.md`.

A version of this checker extended to square constraints and to n = 36, in the self-contained package `lean/kc36/`,
proves `V_36 ≥ 133/100`, and hence `C₁ ≥ 1.33`, by the Lean kernel alone, in 2,274,566 generated modules. `#print
axioms` cannot be run on it, since no single process can import all modules; scans of all its compiled modules show that
it uses no axioms beyond the three standard ones (`lean/kc36/results/KC36/axioms.txt`). An audit repeated this scan with
its own code. From the same inputs it also rebuilt the module of shared parameters, the 78 top-level check modules and
all 2,274,486 generated shard modules, which check the jobs below the top of the tree, with results byte-identical to
ours. It did not rebuild the final assembly module, which imports all the others, but replayed it in Lean's kernel. The
Zenodo record holds `kc36_oleans.sha256.gz`, the SHA-256 hashes of all 2,274,566 compiled modules (the 2,274,565 that
the audit rebuilt and the final one); `lean/kc36/README.md` explains the build and how to compare rebuilt modules with
that list.

### Running the search

The search needs Python 3 with `numpy`, `scipy` and `highspy`. On one machine:

    PYTHONPATH=checker python3 search/bnbtree39f.py init run39 39 267/200 --depth 8 \
        --opts '{"tree_only": false, "d_compat": true, "stale_mc": true}'
    PYTHONPATH=checker python3 search/bnbtree39f.py work run39 --workers 64 --max-nodes 500
    python3 search/d2tree.py run39 run39_tree --workers 64
    python3 tools/idcheck_tree.py run39 run39_tree --workers 64 --strict-names

The writer stores most leaves as D records, with dual vectors stored as integers over a power of 2, which
`checker/verify_tree.py` also reads; `d2tree.py` turns the logs into the tree-only certificate that is archived, and
`idcheck_tree.py` confirms that both copies have the same tree (`docs/TREE_FORMAT.md`, section 5). A worker reads its
node budget from the file `max_nodes.ctl` in the certificate directory if that file exists, so a coordinator can change
the budget during the run.

`init` expands the tree to depth 8 and queues the open nodes as jobs, and `work` processes the queue. A job that
reaches the node budget queues its open nodes as new jobs. For the certificate of `V_39 ≥ 267/200`, a coordinator moved
the job files between up to 487 servers with 62,018 worker processes. The coordinator depends on our environment and
is not included. The run took 4.75 hours and about 187,800 CPU-hours. The certificate of `V_36 ≥ 133/100` came from
`search/bnbtree.py` with `n = 36`, depth 8 and a budget of 500 nodes per job, on up to 203 servers with 40,432 threads
in 5.05 hours (about 36,000 CPU-hours).

The certificate of `V_30 ≥ 33/25` was written by `search/bnbcert2.py` (with `bnbopt.py` and `implied.py`):

    PYTHONPATH=checker python3 search/bnbcert2.py init run30 30 33/25 --depth 8 \
        --opts '{"psd": "m3", "psd_rounds": 1, "psd_k": 1, "compress": true, "cut_table": true}'
    PYTHONPATH=checker python3 search/bnbcert2.py work run30 --workers 64 --max-nodes 600

`code_md5.txt` in that archive records the code of the run, which revised `bnbopt.py` midway (`docs/RUNS.md`). Where two
servers processed the same job, one copy per region was kept (`keep.txt` in that archive), and the Python checker
confirms that the kept jobs partition the region.

## The signed third autocorrelation constant

### Proof outline (Section 6 of the paper)

Normalize `∫ f = 1`, let `M` be the essential supremum of `f∗f`, and let `w = 1_[−1/2,1/2] − (f∗f)/M ≥ 0`, so that
`∫ w = 1 − 1/M`. Then `F² = M (S − ŵ)`, where `F` is the Fourier transform of `f` and `S(z) = sin(πz)/(πz)`. Every zero
of `F²` has even order, but `S` has simple zeros at the nonzero integers. The certificate shows that, if `∫ w ≤ τ`,
then `S − ŵ` has a zero of odd order, which is impossible. So `M > 1/(1 − τ)`.

1. **Level 1.** On a circle `T1` around the zero 1 of `S`, some function `S − λŵ` with `0 < λ ≤ 1` vanishes at a
   point `z` (a crossing). On the arcs of type E a number `u` gives a real-linear functional that separates `S(z)` from
   all values `λŵ(z)` with `∫ w ≤ τ`, so the crossing cannot happen there.
2. **Level 2.** On an arc of type H, a crossing confines `ŵ(z_c)` to a disc around `σ S(z_c)` with `σ ≥ 1`. On a tile,
   an ellipse around the zero 3 of `S`, numbers `u, v` show that no admissible measure with this constraint makes
   `S − ŵ` vanish on the tile. A representative measure shows that `S − ŵ` then has an odd number of zeros inside the
   tile.
3. **Nested trees.** Where the separation fails on part of a tile, Lemma 6.9 of the paper gives a point `z` on one of
   the failing tile arcs and a number `κ ≥ 0` with `ŵ(z) = S(z) + κ G_ν(z)`, where `ν` is the representative measure
   (a tube condition). Under this constraint the argument of level 2 is repeated, in a tree of nodes: a node is empty
   (no admissible measure meets its constraints), splits the arc of one of its tube conditions in two, or carries a
   witness, whose failing tile arcs get children with one more tube condition. The certificate of the bound 4/3
   (τ = 1/4) has no pinned points, and its tiles are ellipses near 3, 4.5 and 6.4 and their mirror images.

The certificate of the weaker bound 25/19 (τ = 6/25), which the Lean proofs read, has a third level instead: on its
arcs of type H3 the possible values of `ŵ` at the two points `P_1 = 3.06 − 0.6i` and `P_2 = 3.18 + 0.24i`, or at
their mirror images, are divided into products of two squares by a tree that splits one of the squares into four at
each node. Each leaf either contains no admissible values (an exclusion with numbers `v` and `y_j`) or carries a
witness on a tile, as in level 2 with an extra term for each point.

### Checking the certificate

The certificate is in the archive at [doi:10.5281/zenodo.23585545](https://doi.org/10.5281/zenodo.23585545) as
`one_sided_tau1_4_parts.tar` (25,152,471,040 bytes). The tar holds 2,048 parts, `cert_t25_sub_000.json.gz` to
`cert_t25_sub_2047.json.gz`, gzip-compressed JSON files in the format of `signed/nested/FORMAT_NESTED.md`, and their
`SHA256SUMS`. Every part has the same header, and part N holds the arcs i of the certificate file with i mod 2048 = N.
That file, `cert_t25.json.gz` (25,148,763,058 bytes, SHA-256
99c7495253679271d49066857eed915779d7418c878d825e00e6430d23603ef6), is not archived, but the JSON rebuilt from the 2,048
parts is identical to the decompressed full certificate. `signed/nested/PARTS_SHA256SUMS` is a copy of the parts'
`SHA256SUMS`; its first line is that of `cert_t25.json.gz`. In an empty directory with the download, with `REPO` the
path to this repository and `NPROC` the number of worker processes:

    sha256sum -c REPO/signed/nested/ARCHIVE.sha256
    tar -xf one_sided_tau1_4_parts.tar
    python3 -I REPO/signed/nested/coverage_subsets2.py 'cert_t25_sub_*.json.gz' 2458 REPO/signed/nested/PARTS_SHA256SUMS 2048
    for f in cert_t25_sub_*.json.gz; do
      b=$(basename "$f" .json.gz)
      python3 -I REPO/signed/nested/check_run2.py REPO/signed/nested/check_nested.py "$f" NPROC --subset --deep \
        > "chk_$b.log" 2>&1 || echo "FAIL first checker $f"
      python3 -I -B REPO/signed/nested/indep_nested.py "$f" NPROC "ind_$b.jsonl" --subset --deep \
        > "ind_$b.log" 2>&1 || echo "FAIL second checker $f"
    done

`coverage_subsets2.py` first checks that there are 2,048 parts and that each has the SHA-256 listed in the manifest,
then that all parts have the same header, that the header meets the global conditions, and that the arcs of all parts
together subdivide [0, 1]; it accepts if it prints `COVERAGE OK` and exits with status 0. `check_run2.py` runs
`check_nested.py` only if its SHA-256 is that of the checker of record and refuses python -O. It also forces the fork
start method of Python's multiprocessing (the default on Linux up to Python 3.13), and it exits with status 0 only if
the checker printed `SUBSET: n of n arcs pass` with equal numbers. `indep_nested.py` exits with status 0 only if every
arc of the part passes; its single assertion, which python -O would skip, cannot change a verdict.

Our claim rests on the coverage check and on `check_nested.py`, which accepted every part: all 2,048 runs ended with
status 0 and `SUBSET: n of n arcs pass`, 2,458 arcs in all. We ran `indep_nested.py` on a random sample of 103 parts,
`random.Random("t25-audit-indep-sample-2026-10-22").sample(range(2048), 103)`; `signed/nested/INDEP_SAMPLE.txt` lists
their numbers N in the order of selection, and `indep_nested.py` accepted every arc of these parts (121 arcs). The loop
above runs both checkers on every part; on the parts of the sample the second used about 2 to 3.4 times as much CPU time
as the first (`docs/RUNS.md` gives the basis).

The runs of record of the first checker used Python 3.12.13 and python-flint 0.9.0, NPROC = 7 and one thread per
process. They took 3 h 27 min on two servers with 384 threads and four with 96 threads, about 2,300 CPU-hours (user and
system time on the first two servers, wall-clock time times threads on the others), with at most 8.3 GB of memory per
part (the proportional set size of the eight processes of one run).

Before the release we ran the commands above as written, in a new directory with a clean copy of `signed/nested/` and
the downloaded archive, with NPROC = 7 and the loop restricted to four parts: 228, the largest (69.1 MB), and 1413, 1843
and 1970. The archive check and the coverage check of all 2,048 parts passed; `check_nested.py` accepted the four parts,
and `indep_nested.py` parts 1413, 1843 and 1970.

The two checkers use ball arithmetic from python-flint with different enclosure methods. `check_nested.py` extends
`signed/checker/check_three_level.py`; `indep_nested.py` was written separately, after reading the code of an earlier
version of `check_nested.py`, and `signed/nested/FORMAT_NESTED.md` lists the 36 lines they share. Neither imports
anything from the search program, but the search program imports `check_nested.py` and applies its checks to each node
before writing it.

The certificate was produced by the programs in `signed/nested/search/`, in the versions that ran, with only comments,
docstrings and path strings changed (`RELEASE_TABLE.tsv` and `AST_CHECKS.txt` there list the changes):
a coarse pass over the arcs of T1 and a first phase that closed some arcs and left the hard tile arcs of the others
as tasks (`phaseA/`, an earlier version of the search programs); a second phase on these tasks for the upper half of
T1, first with `phaseB_V22/` and, for the last 2,927 pieces, with `phaseB_V23/`, which only skips attempts that cannot
succeed inside the subtrees of arc splits; the splitting of pieces that exceeded the node budget (`splits/`); and the
assembly, which mirrors the upper half and writes the certificate and its 2,048 parts (`assembly/`).
`signed/nested/search/RUNS.md` gives the commands and settings of every step. The search needs Python 3.12 with numpy,
scipy, highspy and python-flint; none of it is needed to check the certificate. The copies of `check_nested.py` in
`search/` are the versions that the search programs imported (an earlier one in `phaseA/`). The checker of record,
`signed/nested/check_nested.py`, differs from the copies in `phaseB_V22/` and `phaseB_V23/` in three ways: it rejects
child records whose kind is not `"iv"`, it refuses to run under python -O, and it ends with an error status in the
`--subset` mode when an arc fails.

### Checking the certificate of the bound 25/19

The certificate is in the archive at [doi:10.5281/zenodo.23585545](https://doi.org/10.5281/zenodo.23585545),
compressed with gzip: `one_sided_tau6_25.json.gz` (2,686,181,087 bytes; 10,644,925,969 bytes after decompression). Both
checkers read the compressed file directly. In the directory containing the download:

    sha256sum -c REPO/signed/CERTIFICATES.sha256
    python3 -I REPO/signed/checker/check_three_level_lowmem.py one_sided_tau6_25.json.gz NPROC
    python3 -I REPO/signed/checker/indep_three_level.py one_sided_tau6_25.json.gz NPROC --out indep_results.jsonl

Here `REPO` is the path to this repository and `NPROC` the number of worker processes. When run with the commands above,
a checker accepts if it exits with status 0 and prints a line starting with `OK` (first checker) or `OK (FULL)` (second
checker). A certificate counts only if both checkers accept it. `signed/FORMAT.md` specifies the format and what the
checkers verify. The checkers need Python 3 with `python-flint`; the timed runs below used Python 3.13.5 and
python-flint 0.9.0.

Both checkers use ball arithmetic from python-flint, with different enclosure methods, and neither imports anything from
the search programs in `signed/search/`, which are not part of the proof. `indep_three_level.py` was written after
`check_three_level.py`. It follows the first checker in the reading of the file, the walk over the tree of leaves, the
corner rule for boxes and the outline of the winding count (about fifty short lines coincide). Its enclosures of arcs
and tiles, its bounds in t, its coverage test for the leaves and its acceptance test for the pieces of the winding count
are its own. For the radius r it takes the larger of its own disc-based bound and the ball-based bound of the first
checker, which it re-implements; `signed/FORMAT.md` explains why this is sound.

`check_three_level_lowmem.py` calls `check_three_level.py` unchanged but starts its worker processes with the forkserver
method, so that they do not copy the parsed certificate. The plain `check_three_level.py` gives the same verdict; under
the fork start method, the default on Linux up to Python 3.13, each of its workers can come to hold a copy of the parsed
certificate. The second checker starts its workers as separate programs and writes chunk files into the directory
`indep_results.jsonl.parts`. Neither command above depends on the default start method of Python's multiprocessing.

In both checkers the main process holds the parsed certificate, about 40 GB, and more while it parses the file. We did
not measure the totals for this certificate. For the certificate with τ = 7/30 each checker needed about twice the
memory of its main process with 360 workers: each worker of the first checker added about 64 MB, and the workers of the
second checker hold the arcs a second time (`docs/RUNS.md`). The arcs of this certificate are about twice as large on
average, so plan for roughly 80 GB or more for either checker with a few hundred workers. With 382 worker processes on a
server with 384 threads, the two checks took about 38 and 13 minutes of wall-clock time.

The certificate was produced by the programs in `signed/search/`, which need `numpy`, `scipy`, `highspy` and
`python-flint`. `gen_three_level_m9.py` (configuration `cfg_m9_T1b_024.json`) builds all arcs. It chooses `u`, `v` and
`y_j` by linear programs, solved with HiGHS (through scipy, and for the third level directly through highspy in
`hslp.py`), subdivides arcs, squares and tile arcs until a ball-arithmetic check succeeds, and takes the representative
measures from a linear program. The configuration lists the tiles, and the key `tiles_near` names those that are tried
only on arcs whose centre `z_c` has `|Im z_c| < near_im`. `merge_cert_m2.py` assembles the certificate from the output
file:

    python3 -I gen_three_level_m9.py cfg_m9_T1b_024.json
    python3 -I merge_cert_m2.py cfg_m9_T1b_024.json one_sided_tau6_25.json.gz m9_T1b_024.jsonl

Run these commands inside `signed/search`. The generator imports `gen_two_level.py` and `hslp.py` from the same
directory and writes its results to the file named by the key `out` of its configuration, with the suffix `.jsonl`. The
key `procs` sets the number of worker processes (300 in the configuration). The run took about 3.3 hours with 300
processes (about 1,000 CPU-hours), and no arc failed. The generator's workers inherit its configuration globals through
the fork start method (see above); under forkserver, the default from Python 3.14 on, they would silently run with the
default settings, so use Python 3.13 or earlier for a rerun.

A rerun should again give a certificate that the checkers accept, but not necessarily the same one: in each worker
process every linear program of `hslp.py` starts from the last basis of a program of the same kind and size, and the
order in which the workers take the arcs varies. The gzip header of the merged file also holds a time stamp and a file
name, so `signed/FORMAT.md` gives the SHA-256 of the decompressed JSON as well.

### Lean formalizations of the signed bounds

Theorem 1.3 of the paper, the bound 4/3, has no Lean proof. The weaker bound C₃ ≥ C₃′ ≥ 25/19 is verified in Lean 4 with
Mathlib in `signed/lean_25_19/`, from `one_sided_tau6_25.json.gz`. The sources formalize the argument of Section 6 of
the paper with winding numbers, without the argument principle or the Jordan curve theorem. A checker proved sound in
Lean re-derives every condition of the certificate from the definitions, and one generated module per interval of `T1`
and one for the global data apply it to `one_sided_tau6_25.json.gz`. The theorems `C64Data.mainStatement`,
`C64Data.mainStatementEss` and `C64Data.constStatement` state the bound for every real upper bound of `f ∗ f` almost
everywhere, the same with essential suprema, and `C₃ ≥ C₃′ ≥ 25/19`. The 2,375 finite certificate checks are evaluated
by native_decide (one auxiliary axiom per check). Apart from these auxiliary axioms the theorems use only the three
standard axioms. The interval enclosures of the checker work at 80 bits here and at 64 bits for the certificate below.
The precision is part of the generated data, and the soundness proof holds for every precision. The modules took about
124 CPU-hours to build (27 minutes on one server, 282 modules at a time).

A rebuild from scratch, with the data regenerated from the certificate, re-checked every module in Lean's kernel. With
the auxiliary axioms taken as given, the exported proof is accepted by Lean's kernel (`leanchecker`) and by two other
kernel implementations, nanoda and lean4lean, and a corrupted export is rejected by all three.

`signed/lean_kernel_25_19/` proves the same three statements, as `KData.mainStatement`, `KData.mainStatementEss` and
`KData.constStatement`, by Lean's kernel alone and from the three standard axioms only. It uses a port of the checker to
natural numbers and signs, on which the kernel's arithmetic is fast. The lemmas `C64KChk.checkArc_eq` and
`C64KChk.checkGlob_eq` prove that the port computes the same results as the checker. The certificate is checked by
`decide +kernel` in 41,353 generated modules: the global data, one data module per interval of `T1`, 36,873 modules of
piece theorems, 2,104 assemblies and the check of the global data. Some pieces take a crossing radius computed in
advance (`rprime.json`, not trusted) as a literal, and a separate theorem proves that the radius function returns that
value. The main module also checks that the intervals subdivide [0, 1].

Building the modules took about 13,900 CPU-hours (3.2 hours on 12 servers with 384 threads each). For this proof a
re-check covered only a sample: a seeded random 10% of the piece modules was checked again by Lean's kernel, while the
other piece modules, and the check that the three final theorems depend only on the standard axioms, rest on our own
build.

A certificate of the same kind with τ = 7/30, `one_sided_tau7_30.json.gz` (1,299,987,309 bytes, in the archive), gives
the weaker bound 30/23. The programs that produced it, `gen_three_level_m7.py` and `merge_cert_m.py` with
`cfg_m7_7_30.json`, are in `signed/search` of the repository archived at
[doi:10.5281/zenodo.23549127](https://doi.org/10.5281/zenodo.23549127). `signed/lean/` and `signed/lean_kernel/` prove
C₃ ≥ C₃′ ≥ 30/23 from it with the same checker and the same port, with 30/23 and τ = 7/30 in place of 25/19 and τ =
6/25. Their theorems have the same names as above.

In `signed/lean/` the 2,627 finite certificate checks are evaluated by native_decide (one auxiliary axiom per check),
and the build took 77 minutes on two servers with 140 threads in total. Its exported proof, too, is accepted by
`leanchecker`, nanoda and lean4lean.

`signed/lean_kernel/` depends only on the three standard axioms and checks the certificate by Lean's kernel alone. Its
15,663 generated modules are one data module per interval of `T1`, 10,649 modules of piece theorems, 2,386 assemblies,
the global data and its check. They took about 11,300 CPU-hours to build (6.4 hours on 24 servers with 96 threads each)
and were rebuilt from regenerated sources on other machines. nanoda and lean4lean accepted the soundness chain, the
equality lemmas, the check of the global data and one interval of type E (`A1193`). nanoda also accepted an interval of
type H (`A0000`), with its piece modules and its assembly. The complete export, about 5.7 million constants, was not
checked by a second kernel.

Each of the four directories has a README with the statements, the build steps and the expected hashes.

## Repository layout

- `search/`: the branch-and-bound programs for C₁. `bnbtree.py` writes tree-only certificates (it wrote the certificate
  of `V_36`); `bnbtree39f.py` wrote the logs of the certificate of `V_39`, and `d2tree.py` makes the tree-only copy of
  such logs; `bnbcert2.py`, `bnbopt.py` and `implied.py` write format 2; `bnbcert.py` writes format 1. They import the
  constraint definitions from `checker/verify.py`.
- `checker/`: `verify_tree.py` (tree-only certificates), `verify_tree_dump.py` (the same with the dual dump),
  `verify_cmp.py` (format 2), `verify.py` (format 1), and `second/`, a second checker for tree-only certificates
  with different exact arithmetic and linear-programming code.
- `docs/CERT_FORMAT.md` and `docs/TREE_FORMAT.md`: the certificate formats for C₁; `docs/RUNS.md`: notes on the settings
  and incidents of the runs reported in the paper.
- `tools/`: multistart search for the discrete values `V_n` (`vn_search.py`, `vn_global.py`), exact evaluation of mass
  vectors (`check_point.py`, `check_points.py`) and the same-tree check of two copies of a certificate
  (`idcheck_tree.py`).
- `data/vn_points/`: the explicit mass vectors behind the upper bounds for `V_n` in the paper (exact rationals).
- `lean/`: the Lean 4 + Mathlib formalization; see `lean/README.md`. `lean/kc36/` is a separate package with the
  kernel-only proof of `V_36 ≥ 133/100`.
- `signed/`: for the nested certificate of the bound 4/3, its two checkers, the programs that produced it and its
  format (`nested/`); for certificates in the sense of Definition 6.6, the checkers (`checker/`), the search programs
  of the certificate of the bound 25/19 (`search/`) and the format specification (`FORMAT.md`); two Lean proofs of
  the weaker bound 25/19 (`lean_25_19/`, and `lean_kernel_25_19/` for the kernel-only one) and two of the weaker
  bound 30/23 (`lean/` and `lean_kernel/`). The certificates are in the archive.
- `paper/`: LaTeX source of the paper.

## Versions

The archive record of this repository has one version for each version of the paper, under the concept DOI
[doi:10.5281/zenodo.23480604](https://doi.org/10.5281/zenodo.23480604). The certificates of superseded signed bounds
stay in the versions that added them.

- Version 9 (doi:10.5281/zenodo.23585545) raises the bound for the signed constants from 25/19 to 4/3, with the nested
  certificate in `one_sided_tau1_4_parts.tar` (2,048 parts) and, in `signed/nested/`, its two checkers and the programs
  that produced it. It also adds the kernel-only Lean proof of `C₁ ≥ 1.33` in `lean/kc36/`, with the list
  `kc36_oleans.sha256.gz` of the hashes of its compiled modules, and reports that `leanchecker`, nanoda and lean4lean
  accept the exported proof of the theorems in `signed/lean_25_19/`. Its other data files are those of version 8.
- Version 8 (doi:10.5281/zenodo.23565255) added two Lean proofs of the signed bound 25/19, one with `native_decide` in
  `signed/lean_25_19/` and one checked by Lean's kernel alone in `signed/lean_kernel_25_19/`, and a kernel-only proof of
  30/23 in `signed/lean_kernel/`.
- Version 7 (doi:10.5281/zenodo.23559940) raised the bound for the signed constants from 30/23 to 25/19, with the
  certificate `one_sided_tau6_25.json.gz`.
- Version 6 (doi:10.5281/zenodo.23549127) raised the bound for C₁ from 1.33 to 1.335, with the certificate of
  `V_39 ≥ 267/200`, its Lean proof and the list of the files that this proof reads. It also added the Lean proof of the
  signed bound 30/23 in `signed/lean/`.
- Version 5 (doi:10.5281/zenodo.23538900) raised the signed bound from 100/77 to 30/23, with the certificate
  `one_sided_tau7_30.json.gz`.
- Version 4 (doi:10.5281/zenodo.23527374) raised the bound for C₁ from 1.32 to 1.33, with the certificate of
  `V_36 ≥ 133/100`, its Lean proof, the list of the files that this proof reads and the second checker for C₁ in
  `checker/second/`, and the signed bound from 40/31 to 100/77. The parts of the certificate of `V_30 ≥ 33/25` stayed in
  the earlier versions.
- Version 3 (doi:10.5281/zenodo.23523705) raised the signed bound from 400/311 to 40/31.
- Version 2 (doi:10.5281/zenodo.23509732) added the signed constants, with the bound 400/311.
- Version 1 (doi:10.5281/zenodo.23480605) proved `C₁ ≥ 1.32` from the certificate of `V_30 ≥ 33/25`, archived in 78
  parts, with a Python checker and a Lean proof, and `C₁ ≥ 1.31` with a proof checked by the Lean kernel alone (its
  certificate, of `V_28 ≥ 131/100`, is not archived).

## License

Code: Apache-2.0 (see `LICENSE`). Paper and data: CC BY 4.0.
