# Nested certificates for the signed constants

This file specifies the format of the nested certificate of Theorem 1.3 of the paper and what its two checkers verify.
The notation is that of `../FORMAT.md`:

    S(z) = sin(pi z)/(pi z)   (S(0) = 1),      K_t(z) = exp(-2 pi i t z),
    w-hat(z) = int K_t(z) dw(t),               G_w = S - w-hat,
    T1:   z(s) = c + a cos(2 pi s) + i b sin(2 pi s),            0 <= s <= 1   (c real),
    tile: p(q) = cr + a' cos(2 pi q) + i (ci + b' sin(2 pi q)),   0 <= q <= 1.

All numbers are strings that Python's `Fraction` reads exactly, such as "p/q", "p" or "4.57".

## 1. Claim

For an integrable `f : R -> R` that vanishes almost everywhere outside [-1/4, 1/4] and has `int f != 0`, an accepted
nested certificate (variant `"Cp"`, one-sided case) with threshold tau gives `ess sup f*f > (int f)^2 / (1 - tau)`, so
`C_3 >= C_3' >= 1/(1 - tau)`. This is Corollary 6.13 of the paper. The checkers verify the conditions of Definition 6.11
there: those of Definition 6.6 for the arcs of T1, and for each node of a tree the conditions of its kind, with the
bounds of Lemma 6.10 for empty nodes and for the separations on tile arcs.

## 2. File

    {"variant": "Cp", "tau": q, "T1": [c, a, b], "tiles": {name: [cr, ci, a', b'], ...}, "iv_eps": q,
     "arcs": [arc, ...]}

`iv_eps` is the number epsilon of the tube conditions; it must lie in [0, 1/1000], and the checkers take 1/10^9 if the
field is absent. The certificate of the paper has `"iv_eps": "1/1000000"`. An arc covers the parameter interval
[s0, s1] of T1:

    E arc:  {"type": "E", "s0": q, "s1": q, "u": [ur, ui]}
    N arc:  {"type": "N", "s0": q, "s1": q, "sc": q, "pcs": [[pr, pi], ...], "Rs": [q, ...], "tree": node}

The checkers also read the arc types H and H3 of `../FORMAT.md`, in an extended form: the tile arcs of their witnesses
may carry children, and the trees of H3 arcs may contain arc splits and tube conditions. The certificate of the paper
uses E arcs (276) and N arcs (2,182) only. E arcs are the intervals of type E of Definition 6.6 of the paper; N arcs,
like H and H3 arcs, are intervals of type H. In its N arcs `pcs` and `Rs` are empty: no values are pinned (k = 0 in Definition 6.6), and every node
has an empty list of boxes. A node is one of the following.

    {"ivsplit": l, "at": qm, "kids": [node, node]}                                          arc split
    {"split": j, "kids": [node, node, node, node]}                                          split (needs k >= 1)
    {"type": "empty", "boxes": [Q_1, ...], "v": [vr, vi], "y": [[y1r, y1i], ...],
     "vt": [[vt1r, vt1i], ...], "tau_rep": q}                                               empty node
    {"type": "W", "boxes": [Q_1, ...], "tile": name, "tau_rep": q, "tile_arcs": [tile_arc, ...],
     "wrep_t": [t_1, ...], "wrep_m": [m_1, ...], "sigma": q, "mus": [[q_1, kappa_1], ...]}  witness

`tau_rep` is the number tau_N of the node (tau if the field is absent). The measure of a witness is
nu = sum_k m_k delta_{t_k}, with `wrep_t` and `wrep_m` paired in order (`indep_nested.py` requires lists of equal
length; `check_nested.py` pairs them with zip). A tile arc of a witness is either a separation

    [q0, q1, ur, ui, vr, vi, y1r, y1i, ..., vt1r, vt1i, ...]

with one number y_j for each pinned point and one number vt_l for each tube condition of the node, or a child

    {"hard": [q0, q1], "kind": "iv", "child": node}.

The field `kind` must be `"iv"`, the tube condition of the paper; both checkers reject a child record of any other kind
or without the field. A count over all parts found 7,993,894 child records, all of kind `"iv"` (information only;
the checkers enforce the rule).

Tube conditions. The root of a tree has none. The child below the tile arc [q0, q1] of a witness has the tube conditions
of the witness followed by a new one, (A, nu): A = p([q0, q1]) on the tile of the witness, and nu is the measure of the
witness. An arc split `{"ivsplit": l, "at": qm}` replaces the arc p([q0, q1]) of tube condition l (counted from 0, in
this order) by p([q0, qm]) in its first child and by p([qm, q1]) in its second, where q0 < qm < q1. The lists `vt` of
an empty node, the numbers vt_l of a separation and the list `mus` of a witness follow the same order.

Parts. The certificate is archived in 2,048 parts, `cert_t25_sub_000.json.gz` to `cert_t25_sub_2047.json.gz` (N
zero-padded to three digits). Part N holds the arcs i of the certificate file with i mod 2048 = N, in their order there,
and all parts have the same header (every field except `arcs`). Each part is a file of the format above whose arcs need
not cover [0, 1]; the checkers run on each part in their `--subset` mode, and `coverage_subsets2.py` checks the parts
together (section 5).

## 3. What the checkers verify

Both checkers accept only if all of the following hold. With u = ur + i ui and so on:

1. The global conditions of item 1 of `../FORMAT.md`, and 0 <= iv_eps <= 1/1000.
2. The tile arcs of each witness tile [0, 1]. In a run on a whole certificate file, the arcs tile [0, 1] after sorting;
   in the `--subset` mode, which checks the parts, the checkers test only s0 < s1 for each arc, and
   `coverage_subsets2.py` checks that the arcs of all parts together tile [0, 1] (section 5).
3. E arc: the condition of item 3 of `../FORMAT.md`.
4. N arc: s0 <= sc <= s1, zc = z(sc), and R_j >= tau e^{pi |Im p_j|} for every pinned point (there are none here).
5. Every empty node and every witness has tau_N >= tau, and the checker computes a radius r_N with the property of
   Lemma 6.5 of the paper for the arc, with tau_N in place of tau (so r_N >= r_tau).
6. Empty node: Re(conj(v) S(zc)) >= 0; for each tube condition (A_l, nu_l), Re(conj(vt_l) G_{nu_l}(z)) >= 0 for every
   z on A_l; and for every t in [-1/2, 1/2]

       tau_N max(0, Lambda(t)) < Re(conj(v) S(zc)) - |v| r_N + sum_j min over x in Q_j of Re(conj(y_j) x)
                                   + sum_l (min over z on A_l of Re(conj(vt_l) S(z)) - |vt_l| eps),

       Lambda(t) = Re(conj(v) K_t(zc)) + sum_j Re(conj(y_j) K_t(p_j)) + sum_l max over z on A_l of Re(conj(vt_l) K_t(z)).

7. Witness: the masses are nonnegative, the points lie in [-1/2, 1/2] and the total mass is at most tau_N; sigma >= 1
   and |nu-hat(zc) - sigma S(zc)| <= r_N; nu-hat(p_j) lies in Q_j for every j; for each tube condition l, the entry
   [q_l, kappa_l] of `mus` has q_l in the parameter interval of A_l, kappa_l >= 0 and

       |nu-hat(p(q_l)) - S(p(q_l)) - kappa_l G_{nu_l}(p(q_l))| <= eps,

   where p is the parametrization of the tile of A_l; G_nu has no zero on the tile of the witness, and its winding
   number along the tile is odd. For each separation [q0, q1, ...]: Re(conj(v) S(zc)) <= 0, Re(conj(vt_l) G_{nu_l}(z)) <= 0
   for every z on A_l, and for every p = p(q) with q in [q0, q1] and every t

       Re(conj(u) S(p)) - Re(conj(v) S(zc)) - |v| r_N - sum_j max over x in Q_j of Re(conj(y_j) x)
           - sum_l (max over z on A_l of Re(conj(vt_l) S(z)) + |vt_l| eps) > tau_N max(0, phi_p(t)),

       phi_p(t) = Re(conj(u) K_t(p)) - Re(conj(v) K_t(zc)) - sum_j Re(conj(y_j) K_t(p_j))
                  + sum_l max over z on A_l of (-Re(conj(vt_l) K_t(z))).

   Each child is checked as a node with its list of tube conditions.
8. Arc split: l indexes a tube condition of the node, q0 < qm < q1, and both children are accepted.
9. Split: j indexes a pinned point, and the four children, which use the quarters of Q_j in the order lower left,
   lower right, upper left, upper right, are accepted. `check_nested.py` requires the stored boxes of each empty node
   and witness to equal those of its position in the tree; `indep_nested.py` uses the positions in the tree.

## 4. How the checkers verify it

`check_nested.py` extends `../checker/check_three_level.py` to trees of nodes and uses the same ball arithmetic
(python-flint, 80 bits), the same radius bound (with tau_N in place of tau), the same corner rule for the boxes and the
same winding count.

- E arcs are checked as in `check_three_level.py`: ball evaluation on the arc, with t-intervals bisected to depth 22.
- For empty nodes and separations, the inequalities in t are proved on dyadic cells of [-1/2, 1/2] by second-order
  Taylor bounds, with cells down to length 2^-22. Each term with an arc A_l is enclosed on 4 balls that cover A_l; the
  sign condition and the extremum of the term with S over A_l are bounded on 8 balls that cover A_l, or on 64 if that
  fails. A separation is proved on the ball that encloses the tile arc, which is bisected up to 4 times.
- It rejects child records whose kind is not `"iv"` (section 2), refuses to run under `python -O`, and exits with a
  non-zero status if any arc fails, also in the `--subset` mode.

`indep_nested.py` imports nothing from `check_nested.py`, but it was written separately, after reading the code of an
earlier version of `check_nested.py`. 36 lines of at least 25 characters coincide, 23 of them verbatim: the reading
of the certificate fields (11), the tiling test for the tile arcs (5), four error messages, three loop headers, the
set-up of the trees and of their root boxes (3), the multiplier counts (2), the odd-winding test, the test that T1
encloses exactly one nonzero integer, the quadrants of a split, the counts of pinned points and tube conditions, the
library import and the main guard (2), and two one-line steps inside numerical routines (a bisection step in t and
the test |w - n| < 1/4 of the winding count).
Its checks of the inequalities are its own: enclosures, extrema over arcs, bounds in t, radius, winding computation
apart from that line, tube and box bounds and the E-arc test. Its `--deep` scheduling follows the design of
`check_nested.py`. It uses python-flint with 128 bits.

- Extrema over arcs are bounded by second-order Taylor forms in the parameter q of the arc, with branch and bound.
- The inequalities in t are proved on dyadic cells by mean-value bounds, with cells down to length 2^-34.
- r_N is the smaller of two bounds of Lemma 6.5, one with a disc around zc and one with a box that contains the arc of
  T1; at a witness the checker uses |nu-hat(zc) - sigma S(zc)| instead when this is larger. Definition 6.11 admits any
  r_N >= r_tau.
- It requires tau <= tau_N < 1, rejects child records whose kind is not `"iv"`, and exits with status 1 if any arc
  fails. Its only assert is a bookkeeping check in the `--deep` mode; removing it (python -O) cannot change a verdict,
  because a failure there either raises an error on the next line or makes a subtree be checked twice.

## 5. Commands

The archive holds `one_sided_tau1_4_parts.tar`: the 2,048 parts `cert_t25_sub_*.json.gz` and their `SHA256SUMS`, of which
`PARTS_SHA256SUMS` in this directory is a copy. In an empty directory with the download, with `REPO` the path to the
repository:

    sha256sum -c REPO/signed/nested/ARCHIVE.sha256
    tar -xf one_sided_tau1_4_parts.tar
    python3 -I REPO/signed/nested/coverage_subsets2.py 'cert_t25_sub_*.json.gz' 2458 REPO/signed/nested/PARTS_SHA256SUMS 2048
    for f in cert_t25_sub_*.json.gz; do
      python3 -I REPO/signed/nested/check_run2.py REPO/signed/nested/check_nested.py "$f" NPROC --subset --deep \
        > "chk_$(basename "$f" .json.gz).log" 2>&1 || echo "FAIL $f"
      python3 -I -B REPO/signed/nested/indep_nested.py "$f" NPROC "ind_$(basename "$f" .json.gz).jsonl" --subset --deep \
        > "ind_$(basename "$f" .json.gz).log" 2>&1 || echo "FAIL $f"
    done

`coverage_subsets2.py` checks the file count and every part's SHA-256 against the manifest before it reads the parts,
then the common header and the coverage of [0, 1]; it accepts if it prints `COVERAGE OK` and exits with status 0.
`check_run2.py` runs `check_nested.py` only if its SHA-256 is that of the checker of record, refuses python -O, forces
the fork start method of Python's multiprocessing (needed from Python 3.14 on, whose default is forkserver), and exits
with status 0 only if the checker accepted every arc of the part (one line `SUBSET: n of n arcs pass`).
`indep_nested.py` exits with status 0 only if every arc of the part passes. The claim rests on the coverage check and on
`check_nested.py` accepting every part; `indep_nested.py` was run on the seeded random sample of parts listed in
`INDEP_SAMPLE.txt` (103 parts; it accepted every arc of them). The runs of record of the first checker used Python
3.12.13 and python-flint 0.9.0, NPROC = 7 and one thread per process; they took 3 h 27 min on two servers with 384
threads and four with 96 threads, with at most 8.3 GB of memory per part.
