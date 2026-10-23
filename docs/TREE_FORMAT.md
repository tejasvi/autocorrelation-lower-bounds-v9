# Tree-only certificates (bnbtree.py / verify_tree.py)

A tree-only certificate is the branch-and-bound tree of a format-2 certificate (CERT_FORMAT.md in this directory) without
any dual vectors and without any cut data. Each leaf only states "this region is closed". The checker has to find,
for every leaf, a dual vector whose exact bound reaches lam. How it finds one is not part of the certificate; the
soundness rests only on the exact evaluation of that bound and on the region and partition checks.

## 1. What carries over unchanged from CERT_FORMAT.md

* Section 1 (claim): for every p in Delta_n with sum_i (2i - (n-1)) p_i <= 0, F(p) >= lam.
* Section 2 (files): CERTDIR/meta.json with n, lam and the canonical rowkeys (section 4 of CERT_FORMAT.md); job logs
  CERTDIR/jobs/*.jsonl.gz.
* Section 3 (block tree, columns, column bounds, regions, propagation, children).
* Section 4 (rows, including square cuts, and the strict validation of every rowkey in meta.json).
* Section 6, first part (the Neumaier-Shcherbina bound LB(y) for a dual y over rows and cuts in a region). The
  completion of section 6 is NOT used for tree-only leaves.
* Section 7 (partition) and section 8 (soundness).

## 2. Job logs

Line 1 is the header of section 5 of CERT_FORMAT.md (n, lam equal to meta.json, root path). The records are processed
in order with a stack initialised with the job root region. Every record pops one region R, except K records:

| record | meaning |
|---|---|
| `["I", b, s]` | split R at block b and value s (rational string); requires L_b < s < U_b. Push child 0, then child 1 (child 1 is processed next). Empty children are not pushed. |
| `["S"]` | R is delegated to another job (whose header path is the path of R). |
| `["U"]` | tree-only leaf: R is closed (obligation below). No data. |
| `["T"]` or `["T", [id, ...]]` | as U, with a list of suggested square cuts (ids defined by earlier K records of the job); the checker may use them. |
| `["K", id, key]` | (does not pop) defines square cut `id` (JSON integer, unique in the job) with the given key; validated when read. |
| `["L", lb, idx, vals]`, `["L", lb, idx, vals, cutsA]` | explicit leaf (format 1 / cut list A semantics, CERT_FORMAT.md section 5); written for leaves whose float margin is thin. |
| `["F", idx, vals]` | Farkas leaf (CERT_FORMAT.md section 5). |

At the end of a job the stack must be empty, and no record may find an empty stack.

The records C, D and E of format 2 are NOT part of the tree-only format, and an independent checker may reject a
tree-only certificate that contains them. The logs written by bnbtree39f.py (section 5) are format-2 logs with D and K
records, not tree-only certificates; verify_tree.py checks their D records as in CERT_FORMAT.md sections 5 and 6. Split
values in I records and path values in headers are rational strings (as in CERT_FORMAT.md section 2); the writer always
writes multiples of 2^-30 (meta.json splitbits = 30).

The "stats" field of a header is writer bookkeeping. verify_tree.py reads headers with Python's json module and uses
only n, lam and path. In the certificate of V_39 >= 267/200 the field contains the non-standard JSON token Infinity:
stats.minlb is Infinity in the 170,517 jobs that have no leaf. A checker must accept this token in headers (Python's
json module does; a strict JSON parser rejects it). Records never contain Infinity or NaN.

The half-space condition of the claim is the ("sym",) row of meta.rowkeys (CERT_FORMAT.md section 4); there is no
separate symmetry flag in meta.json or in the headers.

**Obligation of a U (or T) leaf.** The checker must exhibit a dual vector y over the rows of meta.rowkeys at the
region R (McCormick rows built from R) and over any finite set of square cuts of its own choosing (each one a valid
row by the square identity of section 4), such that LB(y) >= lam, with LB evaluated exactly (rational arithmetic).
Any y is admissible: wrong signs on one-sided rows are dropped, exactly as in section 6. If the checker cannot find
such a y, verification FAILS. A poor search can therefore only cause a false rejection, never a false acceptance.

## 3. Soundness

For every p in R, the true point (section 3) satisfies every row of section 4 and every square cut. It also satisfies
the column bounds, with t = F(p) <= 3 whenever F(p) < lam <= 3. By weak duality LB(y) <= F(p) for every admissible y,
so LB(y) >= lam shows that R contains no p with F(p) < lam. The I, S and partition rules are those of format 2, so the
closed leaves cover the root region (the half-space part of the simplex).

## 4. The reference checker verify_tree.py

verify_tree.py is verify_cmp.py plus the records U and T. It reuses verify_cmp.py's region
bookkeeping, row semantics, square-cut validation, L/C/D/F/K handling and partition check unchanged.

For a U leaf it proceeds as follows (untrusted search, then an exact check):
1. **Oracle LP.** A HiGHS model is kept for the whole job: dual simplex, Devex pricing, objective_bound = lam + 1e-6,
   warm start in DFS order.
   - P, G, tree, ZA, rlt and sym rows are always present.
   - Window and McCormick rows are added when they are violated at the LP point, by more than 1e-9, at most 400 per
     round; square cuts enter through the separation of step 2. Rows of all three kinds are removed after more than 40
     leaves without dual weight.
2. **Square-cut separation** (when the converged LP value is below lam). For every pair of non-root blocks d < e,
   form M = [[1, m_d, m_e], [m_d, z_dd, z_de], [m_e, z_de, z_ee]] from the LP values.
   - Take the 20 pairs with the most negative smallest eigenvalue below -1e-6.
   - Scale each eigenvector v so that max |v_i| = 1, then round 2^20 v to integers (vi).
   - Key: ["sq", vi0, [[d, vi1], [e, vi2]]], skipped if vi1 = vi2 = 0.
   - The cuts form a per-job pool, and at most 20 separation rounds are made per leaf.
3. **Exact check.** The HiGHS row duals of the rows in the LP are used (zero for absent rows). Row duals are rounded
   to multiples of 2^-64 and cut duals to multiples of 2^-128; these are just another admissible y. LB(y) is then
   evaluated exactly in integer arithmetic over the common denominator 2^128 * lcm(1..2n) * 2^60 * 2^30.
   - Row coefficients have denominators dividing lcm(1..2n) * 2^60: window weights 2n/(c2-c1+2), and McCormick
     products of region bounds, which are multiples of 2^-30.
   - Column bounds are multiples of 2^-30.
   - This integer evaluation equals verify_cmp.py's Fraction evaluation of the same y (cross-checked on 608 leaves).
   - The leaf is accepted iff LB(y) >= lam.

4. **Retry order for a U leaf** (each attempt ends in the exact check of step 3; the first success accepts the leaf):
   (i) the search above (up to 20 separation rounds); (ii) if CERTDIR/hints/<job file>.hints.json lists this leaf, an
   LP over all rows plus the hint's square cuts (each key validated as in section 4 of CERT_FORMAT.md; an invalid key
   only fails this attempt). If both fail, the leaf FAILS and so does the certificate. There is no other fallback.
5. **Hints** (optional, outside the soundness argument). The file is a JSON list [[k, [key, ...]], ...]: k is the
   1-based ordinal of the U leaf among the job's U records in record order, and the keys are square-cut keys. Our run
   writes hints (VT_HINTS_DIR) for every leaf that needed 4 or more separation rounds, using the cuts of its
   certifying dual. They give a different oracle a fixed fallback for the hardest leaves.
   The V_36 certificate of the paper has no hints directory, and its official run used none (that run wrote hints
   into its run directories; no summary records a hint use).
6. **Dual reuse.** The docstring of verify_tree.py says that the previous leaf's certifying dual is tried first; this
   happens only when VT_REUSE is set (see below), and the runs reported here did not set it.
7. **Effort and robustness measured.**
   - n=16: 79% of leaves pass with no separation round, 13% with 1, 6% with 2, 2.5% with 3 or more (max 5).
     The same certificate also gives 0 failures with three other HiGHS settings standing in for "another build":
     dual steepest edge, primal simplex, and Dantzig pricing with random seed 7.
   - n=26 (487,517 leaves): 86.9% with 0 rounds, 7.2% with 1, 4.3% with 2, 1.27% with 3, 0.28% with 4,
     0.1% with 5 or more (max 9); 1.21 LP solves per leaf.
   - The previous leaf's certifying dual never certified the next leaf (0 of 2,158 at n=16), so dual reuse is
     opt-in only (VT_REUSE).

Diagnostics (environment variables that only affect the untrusted search or the reporting, never the exact check):
VT_SOFT (failing leaves are counted; the program never prints VERIFIED; --summary/--combine are refused),
VT_MAX_ROUNDS (separation rounds, default 20), VT_HIGHS_OPTS (extra HiGHS options, JSON), VT_REUSE, VT_HINTS_DIR,
VT_HINT_ROUNDS (default 4).

## 5. The writers bnbtree.py and bnbtree39f.py

bnbtree.py is a standalone variant of the format-2 search program (bnbopt.py, started through bnbcert2.py) with the
option tree_only; its usage text still calls it bnbcert2.py. A leaf whose float bound (in the writer's own LP: lazy rows
plus its square cuts) is at least lam + tree_margin (default 1e-7) is written as ["U"]. A thinner leaf is written as
an L record with its float duals and inline square cuts. bnbtree.py wrote the certificate of V_36 >= 133/100.

bnbtree39f.py wrote the certificate of V_39 >= 267/200. It is bnbtree.py with D records, stale McCormick rows, two HiGHS
fixes, crash-safe staging and recovery, a read-back of every log it writes, and a node budget that the coordinator can
change during the run. Its usage text also calls it bnbcert2.py, and it refers to the format-2 checker as verify2.py
(checker/verify_cmp.py here). With the options {"tree_only": false, "d_compat": true, "stale_mc": true} it writes a leaf
as a format-2 D record (duals int/2^F on listed rows, with K records for its square cuts; CERT_FORMAT.md sections 4-6,
cut list A) when one of its D encodings passes a floating-point re-check, as ["U"] when none does but the float bound is
at least lam + 1e-7, and as an L record when the float bound is thinner. The records of these logs are I, S, K, D, U and
L only, and checker/verify_tree.py reads all of them. The archived certificate is the tree-only copy made by
search/d2tree.py: the header line is copied byte for byte, K records are dropped, every D record becomes ["U"], and
every other record is copied unchanged. tools/idcheck_tree.py confirms that two copies have the same tree. The docstring
of d2tree.py calls the writer `bnbtree.py with {"tree_only": false, "d_compat": true}` and mentions to_tree.py, which is
not in this repository. meta.json is copied from the logs, so the archived certificate's meta.json still says "solver":
"bnbcert2", "format": 2 and "tree_only": false; the checkers ignore these keys.

## 6. Test results

The first five rows are test certificates, not the certificates of Section 5 of the paper.

| certificate | leaves | stored-dual size | tree-only size | result |
|---|---|---|---|---|
| V_16 >= 5/4 | 2,158 | 1.63 MB | 50 KB | VERIFIED |
| V_20 >= 32/25 | 34,239 | 33.2 MB | 333 KB | VERIFIED |
| V_24 >= 13/10 | 705,473 | 990 MB | 6.05 MB | VERIFIED (90,788 CPU s, 129 ms/leaf) |
| V_16 >= 5/4, written by bnbtree.py | 2,190 | - | 51 KB | VERIFIED |
| V_28 >= 131/100, written by bnbtree.py (rehearsal) | 2,669,845 | - | 24.2 MB | VERIFIED (2,342 s on one 384-thread server) |
| V_36 >= 133/100, written by bnbtree.py (the paper; 2,419,679 jobs, one L leaf) | 177,077,986 | - | 2.84 GB | VERIFIED |
| V_39 >= 267/200, written by bnbtree39f.py (the paper; 13,678,676 jobs, two L leaves) | 527,163,006 | 1.42 TB (D logs) | 13.1 GB | VERIFIED (D logs and tree-only copy) |
