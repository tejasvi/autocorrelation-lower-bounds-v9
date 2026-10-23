# Certificate format

This file specifies the certificate format for checkers. Format 1 is written by `search/bnbcert.py` and checked by
`checker/verify.py`. Format 2 adds square cuts and compressed leaves; the certificate of V_30 >= 33/25 (Section 5 of
the paper) uses it, was written by `search/bnbcert2.py` (with `search/bnbopt.py`) and is checked by
`checker/verify_cmp.py`. The certificate of the main theorem, V_39 >= 267/200, and the smaller certificate of V_36 >= 133/100 are tree-only
certificates (`docs/TREE_FORMAT.md`), which reuse sections 1-8 of this file. Format 2 is a
strict superset of format 1: every format-1 certificate is a format-2 certificate with the same meaning. Sections 1-8
specify format 2. Section 9 lists where `checker/verify_cmp.py` differs from this specification.

## 1. Claim

For an integer n >= 2 and a rational 0 < lam <= 3: for every p in the simplex Delta_n with
sum_i (2i - (n-1)) p_i <= 0,

    F(p) = max_{0 <= c1 <= c2 <= 2n-2}  2n/(c2-c1+2) * sum_{c1 <= i+j <= c2} p_i p_j  >=  lam,

the inner sum over ordered pairs (i, j) in {0..n-1}^2. (Reversal symmetry covers the other half-space.)

## 2. Files

    CERTDIR/meta.json            {"n": int, "lam": "p/q", "rowkeys": [...], ...}   (other keys are ignored)
    CERTDIR/jobs/*.jsonl.gz      one gzip'd job log per job (only files matching this glob belong to the certificate)

Numbers: JSON integers, rational strings, or JSON floats. Floats occur only in L/F record values and in cut list A
values; a float means the exact value of the IEEE-754 double that Python's json module parses (every such value is a
dyadic rational); NaN/Infinity are rejected. The field `lb` of L/E/D records is informational and ignored.
Rational strings are written as "p/q" or "p" (Python's verifier accepts Python Fraction syntax). Writers always
write split values and path values as rational strings.

## 3. Block tree, columns, regions

* Blocks: balanced binary tree over bins 0..n-1, built recursively by `build(lo, hi)`: a node for [lo, hi); if
  hi - lo > 1, children `build(lo, mid)` then `build(mid, hi)` with mid = (lo + hi) // 2. Blocks are numbered in
  creation (preorder) order: block 0 is the root [0, n). size(B) = hi - lo. Leaves are blocks of size 1;
  leaf_of_bin(i) is the leaf block of bin i. nB = number of blocks = 2n - 1.
* Columns (semantic keys; the true point of p is given in brackets):
  `("m", B)` [m_B = sum_{i in B} p_i], `("Z", i, j)` with i <= j [p_i p_j], `("ZA", D, E)` with D <= E,
  not both leaves [m_D m_E] (canonical rows only use D, E >= 1), `("P", c)` [sum_{i+j=c} p_i p_j, ordered], `("G", c)` [P_0 + ... + P_c], `("t",)` [F(p)].
  canon_pair(D, E): sort so D <= E; if both are leaves, ("Z", bin(D), bin(E)) with the bins sorted; else ("ZA", D, E).
* Column bounds in a region (L, U): m_B in [L_B, U_B]; Z, ZA, P, G in [0, 1]; t in [0, 3].
* Regions: L, U are vectors over blocks. Root region = propagate(L = 0, U = 1). Child of region R at block b and
  value s (requires L_b < s < U_b strictly): side 0 sets U_b = s, side 1 sets L_b = s; then propagate.
  propagate: set L_0 = max(L_0, 1), U_0 = min(U_0, 1); repeat up to 64 sweeps (stop when a sweep changes nothing;
  failing to converge is an error) over all internal blocks b in increasing order with children c1, c2:
      L_b, U_b   := max(L_b, L_c1 + L_c2), min(U_b, U_c1 + U_c2)
      L_c1, U_c1 := max(L_c1, L_b - U_c2), min(U_c1, U_b - L_c2)
      L_c2, U_c2 := max(L_c2, L_b - U_c1), min(U_c2, U_b - L_c1)
  (all six new values computed from the old ones, then assigned). If some L_B > U_B the region is empty.

## 4. Rows

Every row is lo <= a.x <= up with exact rational data (lo or up may be absent = infinite).

| key | row | lo, up |
|---|---|---|
| `("win", c1, c2)`, 0 <= c1 <= c2 <= 2n-2 | w G_c2 - w G_{c1-1} - t, w = 2n/(c2-c1+2), no G_{-1} term when c1 = 0 | -inf, 0 |
| `("P", c)`, 0 <= c <= 2n-2 | P_c - sum_{i <= j, i+j=c} (1 if i=j else 2) Z_ij | 0, 0 |
| `("G", c)` | G_c - P_c - G_{c-1} (no G_{-1} term for c = 0) | 0, 0 |
| `("tree", b)`, b internal | m_b - m_c1 - m_c2 | 0, 0 |
| `("ZA", D, E, s)`, s in {D, E}, s internal | if D = E: [D D] - [s1 s1] - 2 [s1 s2] - [s2 s2]; else, with o the other block: [D E] - [s1 o] - [s2 o]; here [X Y] = canon_pair(X, Y), s1, s2 the children of s; coefficients of equal columns are added | 0, 0 |
| `("rlt", i)` | sum_{j=0}^{n-1} Z_{min(i,j),max(i,j)} - m_{leaf_of_bin(i)} | 0, 0 |
| `("sym",)` | sum_{i: 2i != n-1} (2i - (n-1)) m_{leaf_of_bin(i)} | -inf, 0 |
| `("mc", D, E, q)`, 0 <= D, E < nB, q in 0..3 | McCormick with the current region (below) | -inf, rhs |

McCormick (z = canon_pair(D, E)): if D != E:
q=0: -z + L_E m_D + L_D m_E <= L_D L_E; q=1: -z + U_E m_D + U_D m_E <= U_D U_E;
q=2: z - U_E m_D - L_D m_E <= -L_D U_E; q=3: z - L_E m_D - U_D m_E <= -U_D L_E.
If D = E: q=0: -z + 2 L_D m_D <= L_D^2; q=1: -z + 2 U_D m_D <= U_D^2; q=2 and q=3: z - (L_D + U_D) m_D <= -L_D U_D.

Every rowkey in meta.json is validated strictly (integer arguments, ranges above); an invalid key rejects the
certificate.

**Square cut** (format 2), key `["sq", v0, [[B1, v1], ..., [Bk, vk]]]`: v0 and all Ba, va are JSON integers;
1 <= k; 1 <= Ba < nB pairwise distinct; at least one va != 0. With the nonzero terms only (in the listed order):
row = sum_a va^2 [Ba Ba] + sum_{a<c} 2 va vc [Ba Bc] + sum_a 2 v0 va m_Ba, lo = -v0^2, up = +inf.
Validity: at the true point the row value plus v0^2 equals (v0 + sum_a va m_Ba)^2 >= 0. The row does not depend
on the region.

**Canonical row list** (needed for D records): exactly, in this order,
1. ("win", c1, c2) for c1 = 0..2n-2, c2 = c1..2n-2;
2. ("P", c), c = 0..2n-2;  3. ("G", c), c = 0..2n-2;  4. ("tree", b) for internal b in increasing order;
5. ("ZA", D, E, s) for (D, E) in PAIRS with not both leaves, where s = E if D is a leaf, D if E is a leaf,
   otherwise D if size(D) >= size(E) else E;
6. ("rlt", i), i = 0..n-1;  7. ("sym",);  8. ("mc", D, E, q) for (D, E) in PAIRS, q = 0..3;
where PAIRS = [(D, E) for D in 1..nB-1 for E in D..nB-1] (lexicographic). (Identical to search/bnbcert.py.)

## 5. Job logs

Line 1: header `{"n": n, "lam": "p/q" (equal to meta), "path": [[b, "s", side], ...], ...}` (other keys ignored).
The job root region is obtained from the root region by applying the path (side in {0, 1}).
Then one record per line. Records are processed in order with a stack initialised with the job root region;
every record except K pops one region R from the stack:

| record | meaning |
|---|---|
| `["I", b, s]` | split R at block b (JSON integer, 0 <= b < nB) and value s (rational string); requires L_b < s < U_b. Push child 0 then child 1 (child 1 is processed next); empty children are not pushed. |
| `["S"]` | R is delegated to another job (whose header path is the path of R). |
| `["L", lb, idx, vals]` or `["L", lb, idx, vals, cutsA]` | leaf: dual y_idx[j] = vals[j] (number or rational string); duplicates in idx allowed (each entry is its own term); cutsA: square-cut duals (cut list A). |
| `["F", idx, vals]` | Farkas leaf: the bound with zero objective (below) must be > 0. vals numbers or strings (format 2 writes integers). |
| `["K", id, key]` | (does not pop) defines square cut `id` (JSON integer, unique within the job) with the given key; validated when read. |
| `["E", lb, F, idx, ints]` or `["E", lb, F, idx, ints, Fc, cuts]` | explicit integer leaf: y_idx[j] = ints[j] / 2^F. |
| `["D", lb, F, idx, ints]`, `["D", lb, F, idx, ints, cutsA]` or `["D", lb, F, idx, ints, Fc, cuts]` | compressed leaf: as E, then the duals of the auxiliary rows are completed (section 6). |

E/D details: lb is informational (ignored). F, Fc are JSON integers in [0, 1024]. idx is a list of row indices
into meta.rowkeys (integers, 0 <= k < number of rows), pairwise distinct; ints is a list of JSON integers (not
booleans) of the same length. For D: no index may be a P, G or ZA row, and meta.rowkeys must equal the canonical
row list. cuts (present iff the record has 7 fields) is a non-empty list of `[id, m]` with JSON integers, ids
defined by an earlier K record of the same job and pairwise distinct; the cut's dual is m / 2^Fc (cut list B).

Cut list A (6-field D, 5-field L): a non-empty list of `[ref, value]`; ref is either a JSON integer naming a cut
defined by an earlier K record of the same job (refs pairwise distinct) or an inline square-cut key (validated as in
section 4); value is a JSON number (float: the exact value of the parsed IEEE double) or a rational string; it is
the dual of that cut row exactly.

At the end of the job the stack must be empty (no missing records), and no record may find an empty stack.

## 6. The bound and the completion

Leaf bound (Neumaier-Shcherbina) for duals y over rows (and cuts) in region (L, U):
for each row r with y_r != 0: if y_r > 0 and lo_r is absent, or y_r < 0 and up_r is absent, the row is dropped
(treated as y_r = 0); otherwise rowpart += y_r * (lo_r if y_r > 0 else up_r) and reduced costs
red_c -= y_r * a_{r,c}. Then red_t += 1 (objective; omitted for F records) and

    LB = rowpart + sum_c min(red_c * lb_c, red_c * ub_c)    (sum over columns with red_c != 0)

The leaf is valid iff LB >= lam (F: iff the zero-objective value is > 0).

Completion for D records (y given on the listed rows and cuts; P, G, ZA rows are equalities, so any value is
admissible there). Let C(col) = sum over the listed rows and cuts with admissible sign (as above) of
y_r * a_{r,col}. Then, exactly:

    y[G_c] = y[G_{c+1}] - C(G_c)    for c = 2n-2 down to 0, with y[G_{2n-1}] := 0
    y[P_c] = y[G_c] - C(P_c)        for c = 0..2n-2
    for the ZA rows in decreasing order of size(D) + size(E) (ties: increasing canonical index):
        y[ZA row (D,E,s)] = -C([D E]) - sum over ZA rows r' that contain the column [D E] as a child term of
                            (coefficient of [D E] in r') * y[r']

This is the unique solution of "reduced cost 0 on every G, P and ZA column" (the system is triangular in this
order). The leaf bound is then evaluated with the listed duals, the cuts and the completed duals together.

## 7. Partition

Each job's root path (as a key: list of (b, s as reduced rational string, side)) must be unique; the multiset
{root path ()} + {paths of all S records} must equal the set of job root paths, with no duplicates; every job must
be reachable from the root job through S delegations (no cycles).

## 8. Soundness summary

Every row is satisfied by the true point of every p in the region (section 4; square cuts by the square identity),
the column bounds hold at the true point, and t = F(p) <= 3 when F(p) < lam <= 3. Weak duality then gives
LB(y) <= F(p) for every admissible y, so LB >= lam excludes the whole region; F records show the region's LP is
infeasible. The completion only selects particular admissible values on equality rows. The partition check
ensures that the leaves cover the root region (the half-space part of the simplex).

## 9. The checker in this repository

`checker/verify_cmp.py` is the checker frozen for the certificate of V_30 >= 33/25. For the records that
`search/bnbopt.py` writes (K records, 5- and 6-field D records, 4- and 5-field L records, I, S and F records) it
evaluates exactly the bounds of this specification: the same rows, the same square-cut semantics, the same
admissibility rule and the same completion. It processes the ZA rows in a depth-first, parents-first order; the
triangular system has a unique solution, so the completed duals are identical. It differs from this specification
only on inputs that `search/bnbopt.py` does not write, and it is sound in each case:
* it requires the D exponent F to lie in [0, 512];
* it accepts duplicate cut references and an empty cut list in a 6-field D record or a 5-field L record (each entry
  is its own term);
* it accepts D records with a non-canonical meta.json as long as all G and P rows are present;
* it accepts "C" records `["C", lb, idx, vals(, cutsA)]`, which are D records with exact-number duals;
* it does not accept E records or 7-field D records (cut list B).
