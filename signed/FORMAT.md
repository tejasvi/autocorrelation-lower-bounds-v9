# Certificates for the signed constants

This file specifies the format of the certificates of Definition 6.6 of the paper and what their checkers verify. The
nested certificate of Theorem 1.3 and its checkers are described in `nested/FORMAT_NESTED.md`. Notation:

    S(z) = sin(pi z)/(pi z)   (S(0) = 1),      K_t(z) = exp(-2 pi i t z),
    w-hat(z) = int K_t(z) dw(t),               G_w = S - w-hat,
    T1:   z(s) = c + a cos(2 pi s) + i b sin(2 pi s),            0 <= s <= 1   (c real),
    tile: p(q) = cr + a' cos(2 pi q) + i (ci + b' sin(2 pi q)),   0 <= q <= 1.

All rational numbers are strings "p/q" or "p" and are read exactly (Python `Fraction`).

## 1. Claim

For an integrable `f : R -> R` that vanishes almost everywhere outside [-1/4, 1/4] and has `int f != 0`, an accepted
certificate (variant `"Cp"`, one-sided case) with threshold tau gives `ess sup f*f > (int f)^2 / (1 - tau)`, so
`C_3 >= C_3' >= 1/(1 - tau)`. This is the one-sided case of Corollary 6.8 of the paper. Each checker verifies the
conditions of Definition 6.6 there, with radii r >= r_tau and r' >= r_tau' >= r_tau computed
from an enclosure of each arc (by the second checker, the larger of the values from two enclosures).

## 2. File

    {"problem": text, "variant": "Cp", "tau": q, "T1": [c, a, b],
     "tiles": {name: [cr, ci, a', b'], ...},
     "arcs": [arc, ...], "complete": true}

An arc covers the parameter interval [s0, s1] of T1 and has one of three types.

    E arc  (level 1):  {"type": "E",  "s0": q, "s1": q, "u": [ur, ui]}
    H arc  (level 2):  {"type": "H",  "s0": q, "s1": q, "sc": q, "tile": name,
                        "tile_arcs": [[q0, q1, ur, ui, vr, vi], ...],
                        "wrep_t": [t_1, ...], "wrep_m": [m_1, ...], "sigma": q, "count": int, "rA_used": number}
    H3 arc (level 3):  {"type": "H3", "s0": q, "s1": q, "sc": q, "pcs": [[pr, pi], ...], "Rs": [q, ...], "tree": node}

An H3 arc pins the values w-hat(p_j) at m points p_j = pr + i pi ("pcs"), with radii R_j ("Rs"); m is the number k of
points in Definition 6.6 of the paper; every H3 arc of the certificate for tau = 6/25 has m = 2. A node of its tree
stands for a product Q_1 x ... x Q_m of squares, where Q_j holds the real and imaginary parts of w-hat(p_j); the root is
the product of the squares [-R_j, R_j] x [-R_j, R_j]. A node is either a split
`{"split": k, "kids": [node, node, node, node]}`, which divides the square Q_{k+1} (k = 0, ..., m-1)
[x0, x1] x [y0, y1] into the four quarters (x0..mx, y0..my), (mx..x1, y0..my), (x0..mx, my..y1), (mx..x1, my..y1) and
keeps the other squares, or a leaf:

    {"type": "empty", "boxes": [Q_1, ..., Q_m], "v": [vr, vi], "y": [[y1r, y1i], ..., [ymr, ymi]]}  (exclusion)
    {"type": "W", "boxes": [Q_1, ..., Q_m], "tile": name, "tau_rep": q,
     "tile_arcs": [[q0, q1, ur, ui, vr, vi, y1r, y1i, ..., ymr, ymi], ...],
     "wrep_t": [...], "wrep_m": [...], "sigma": q, "count": int}                                  (witness)

with each box Q_j = [x0, x1, y0, y1].

The fields `problem`, `complete`, `count` and `rA_used` are informational, and the checkers ignore them. In particular
the checkers compute the radii r and the zero counts of the witnesses themselves.

## 3. What the checkers verify

Both checkers accept a certificate only if all of the following hold. With u = ur + i ui, v = vr + i vi,
y_j = yjr + i yji:

1. 0 < tau < 1; a, b > 0; exactly one nonzero integer lies in (c - a, c + a), and c - a, c + a are not nonzero
   integers. Since all zeros of S are real, T1 then encloses exactly one zero of S and passes through none. Each tile
   has a', b' > 0.
2. After sorting, the arcs tile [0, 1] (first s0 = 0, last s1 = 1, s0 < s1, consecutive endpoints equal), and the tile
   arcs of each witness tile [0, 1] in the same way.
3. E arc: for every z = z(s), s in [s0, s1], and every t in [-1/2, 1/2],

       Re(conj(u) S(z)) > 0   and   Re(conj(u) (S(z) - tau K_t(z))) > 0.

4. H and H3 arcs: s0 <= sc <= s1. Let zc = z(sc). Each checker computes a radius r(tau) with the property of Lemma 6.5
   (localization) of the paper: for every nonnegative measure w of mass at most tau, every z on the arc and every
   lambda in (0, 1] with S(z) = lambda w-hat(z), the number sigma = 1/lambda satisfies |w-hat(zc) - sigma S(zc)| <= r.
5. H arc (a witness with tau' = tau and no y): for each tile arc [q0, q1], Re(conj(v) S(zc)) <= 0 and, for every
   p = p(q), q in [q0, q1], and every t, with phi_p(t) = Re(conj(u) K_t(p)) - Re(conj(v) K_t(zc)),

       Re(conj(u) S(p)) - Re(conj(v) S(zc)) - |v| r > tau max(0, phi_p(t));

   w_rep = sum m_k delta_{t_k} has m_k >= 0, sum m_k <= tau, t_k in [-1/2, 1/2] (wrep_t and wrep_m paired in order);
   sigma >= 1 and |w_rep-hat(zc) - sigma S(zc)| <= r; G_{w_rep} has no zero on the tile, and its winding number along
   the tile (counterclockwise) is odd.
6. H3 arc: R_j >= tau e^{pi |Im p_j|} for every j (so |w-hat(p_j)| <= R_j for every w of mass at most tau); the leaves
   cover the product of the squares [-R_j, R_j]^2 (check_three_level.py requires the boxes of each leaf to equal those
   of its position in the tree; indep_three_level.py requires the leaves to lie in the product, to be pairwise
   interior-disjoint and to have total volume prod_j (2R_j)^2, and reports differences from the tree positions as a
   cross-check only); and each leaf satisfies:
   - exclusion: Re(conj(v) S(zc)) >= 0 and, for every t, with
     Lambda(t) = Re(conj(v) K_t(zc)) + sum_j Re(conj(y_j) K_t(p_j)),

         tau max(0, Lambda(t)) < Re(conj(v) S(zc)) - |v| r + sum_j min over x in Q_j of Re(conj(y_j) x);

   - witness: tau_rep >= tau; r' = r(tau_rep); for each tile arc, Re(conj(v) S(zc)) <= 0 and, for every p on it and
     every t, with phi_p(t) = Re(conj(u) K_t(p)) - Re(conj(v) K_t(zc)) - sum_j Re(conj(y_j) K_t(p_j)),

         Re(conj(u) S(p)) - Re(conj(v) S(zc)) - |v| r' - sum_j max over x in Q_j of Re(conj(y_j) x) > tau_rep max(0, phi_p(t));

     w_rep has nonnegative masses at points of [-1/2, 1/2] with total mass at most tau_rep, sigma >= 1,
     |w_rep-hat(zc) - sigma S(zc)| <= r', w_rep-hat(p_j) lies in Q_j for every j, and the winding number of G_{w_rep}
     along the tile is odd.

## 4. How the checkers verify it

`checker/check_three_level.py` uses ball arithmetic (python-flint, 80 bits).

- Every point set is enclosed in a complex ball: z(s) for s in an interval of T1, p(q) for q in a tile interval, and t
  in a subinterval of [-1/2, 1/2]. An inequality is accepted only if the ball comparison is certain.
- Failing pieces are bisected: in t up to depth 22; in s and q up to depth 4.
- r: Z is the ball that encloses the arc, and it contains every segment [z, zc]. With d >= |z - zc| on Z, Y >= |Im|
  on Z, m_S <= |S| on Z and L >= |S'| on Z, r = d (tau pi e^{pi Y} + sigma_max L) with sigma_max = tau e^{pi Y} / m_S;
  r' uses tau_rep in place of tau.
- min and max of Re(conj(y_j) x) over a box Q_j: the corner is chosen exactly from the signs of y_j, and the value is
  enclosed in a ball.
- The conditions on w_rep are checked in exact rational arithmetic, except the inequality with r' and the box
  conditions for the values w_rep-hat(p_j), which are checked with balls.
- Winding numbers: the tile parameter interval is cut into 1024 pieces, which are bisected until the ball of values
  of G_{w_rep} over a piece has radius less than half its lower distance from 0 (pieces shorter than 2^-24 reject).
  The argument increments over the pieces are added. The total divided by 2 pi must be within 1/4 of an odd integer.

`checker/indep_three_level.py` verifies the same conditions. It was written after `check_three_level.py`. It follows
the first checker in the reading of the file, the walk over the tree of leaves, the corner rule for the extremes of
Re(conj(y_j) x) over a box and the outline of the winding count (about fifty short lines coincide). Except for the
ball-based radius bound, which re-implements the first checker's enclosure and formula, its enclosures of arcs and
tiles, its bounds in t, its coverage test for the leaves and its acceptance test for the pieces of the winding count
are its own. It also uses python-flint (100 bits), with a different enclosure method:

- each arc is enclosed in a disc D(p(qm), V (q1 - q0)/2) with V >= sup |p'| on the arc, and functions of p are bounded by
  the value at the centre plus a Lipschitz bound times the radius; |S'| on a disc D(pm, rho) is bounded by
  |S'(pm)| + rho (pi^2/3) e^{pi Y}, from |S''(w)| <= (pi^2/3) e^{pi |Im w|};
- functions of t are bounded on cells [tc - dl, tc + dl] by f(tc) + dl |f'(tc)| + dl^2 M2 / 2 with M2 >= |f''|;
- r is the larger of two valid bounds: the one with the disc D(zc, d) as the convex set, with local bounds for |S'|, and
  the ball-based bound of the first checker (re-implemented here). Definition 6.6 admits any r >= r_tau. The larger
  value makes the exclusion and tile-arc conditions harder and the crossing condition
  |w_rep-hat(zc) - sigma S(zc)| <= r' easier; every witness of the certificate for tau = 6/25 also passes with the
  disc-based value alone;
- the leaves must lie in the product of the squares [-R_j, R_j]^2, be pairwise interior-disjoint and have total volume
  prod_j (2R_j)^2;
- a winding piece is accepted when |G(pm)| > 2 L_G rho, so that its image lies in a disc of angular half-width below
  30 degrees around G(pm).

`indep_three_level.py` parses the certificate once, runs its own worker processes (no multiprocessing.Pool) on chunk
files that hold the global data and each worker's arcs, and writes its results file and the directory RESULTS.parts,
which holds the chunks, where `--out` points.

Both checkers bound |S'| locally. With a bound on a whole horizontal strip, the first checker's r would be up to about
2.3 times larger (at least twice on 426 of the 2,104 arcs of types H and H3), and 1,574 of the 66,632 exclusions would
fail in a floating-point evaluation; with the local bounds the smallest exclusion slack there is about 2.5e-5.

## 5. Commands

The certificate is in the archive, not in this repository, as `one_sided_tau6_25.json.gz` (gzip-compressed; both
checkers read it directly). The file `CERTIFICATES.sha256` in this directory lists its SHA-256; the decompressed JSON
has 10,644,925,969 bytes and SHA-256 0216886fd430c7f0b42650fa11e5ccfc0f6c1a5a0e319e68728c40266a05ed70. In the
directory containing the download, with `REPO` the path to this repository:

    sha256sum -c REPO/signed/CERTIFICATES.sha256
    python3 -I REPO/signed/checker/check_three_level_lowmem.py one_sided_tau6_25.json.gz NPROC
    python3 -I REPO/signed/checker/indep_three_level.py one_sided_tau6_25.json.gz NPROC --out indep_results.jsonl

`NPROC` is the number of worker processes. `check_three_level_lowmem.py` runs `check_three_level.py` unchanged with
worker processes that do not copy the parsed certificate. In both checkers the main process holds the parsed
certificate, about 40 GB. The totals were not measured for this certificate; by the measurements for the certificate
with tau = 7/30 (docs/RUNS.md), either checker should need roughly twice that with a few hundred workers. The plain
`check_three_level.py` gives the same verdict, but under the fork start method (the default on Linux up to Python 3.13)
each of its workers can come to hold a copy of the parsed certificate. A checker accepts if it prints a line starting
with `OK` and exits with status 0 (the second checker prints `OK (FULL)`). `check_three_level.py` relies on assert
statements and refuses to run under `python -O`; `indep_three_level.py` uses no assert. In the output, `C` and `C'` are
the constants `C_3` and `C_3'` of the paper.
