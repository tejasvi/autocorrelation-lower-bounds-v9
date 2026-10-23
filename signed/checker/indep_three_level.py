#!/usr/bin/env python3
"""Second checker for three-level certificates of the signed third autocorrelation problem (one-sided case, class A_tau).

Written from the statements of Section 6 of the paper (the lemmas, the certificate definition and the proposition on
multi-level certificates), after check_three_level.py.  Its enclosures of arcs and tiles, its bounds in t, its radius
r_mine (below; it also evaluates check_three_level.py's radius r_ship in its own code and uses the larger), its coverage
test for the leaves and its acceptance test for the pieces of the winding count are its own; the
reading of the file, the walk over the tree of leaves, the corner rule for boxes and the outline of the winding count
follow check_three_level.py (about fifty short lines coincide).  It reads CERT.json or CERT.json.gz.

Level-3 arcs may carry several pinned points p_1..p_m ("pcs") with radii R_1..R_m ("Rs") and a tree over the product of
the squares [-R_j,R_j]^2; a split node {"split": k, "kids": [4 nodes]} divides the k-th square into four, and every leaf
carries a product box Q_1 x ... x Q_m ("boxes").  The pinned set of a leaf is {nu in A_tau': sigma >= 1,
|nu-hat(zc) - sigma S(zc)| <= r, nu-hat(p_j) in Q_j for all j} (the certificate definition with k = m pinned points).
An arc with a single point ("pc", "R", leaves with "box") is the case m = 1.

Notation.  K_t(z) = exp(-2 pi i t z),  S(z) = sin(pi z)/(pi z) = int_{-1/2}^{1/2} K_t(z) dt,  A_tau = nonnegative measures on
[-1/2,1/2] of mass <= tau,  mu-hat(z) = int K_t(z) dmu(t),  G_mu = S - mu-hat.  Ellipse e = (cr, ci, a, b):
p(q) = cr + a cos(2 pi q) + i (ci + b sin(2 pi q)), q in [0,1] (counterclockwise since b > 0).

Conditions verified (tau = certificate threshold; all numbers in the certificate are exact rationals):
 global  T1 = (c, 0, a, b) with a, b > 0; the nonzero integers in the open interval (c-a, c+a) are counted exactly (all of
         them, no fixed range) and must be exactly one; c-a and c+a are not nonzero integers (so T1 passes through no zero of
         S); the T1 arcs [s0,s1] tile [0,1]; every tile has a, b > 0; the tile arcs of every witness tile [0,1].
 E arc (u):  Re(conj(u) S(z)) > tau max(0, max_t Re(conj(u) K_t(z)))   for every z on the arc.
 H arc (level 2: sc, tile, tile arcs (u,v), w_rep, sigma) and H3 arc (level 3: sc, points p_j, radii R_j, leaves):
         zc = z(sc), s0 <= sc <= s1, and the radius r_tau of the localization lemma computed HERE with
            d = V max(s1-sc, sc-s0) >= |z - zc| on the arc, V >= sup_arc |z'(s)| (ball over the arc),
            U = closed disc D(zc, d) (convex, contains the arc),
            Y = |Im zc| + d,  L = |S'(zc)| + d (pi^2/3) e^{pi Y} >= sup_U |S'|,  m_S = |S(zc)| - d L <= min_arc |S| (> 0),
            sigma_max = tau e^{pi Y}/m_S,  r = d (pi tau e^{pi Y} + sigma_max L),
         (this is r_mine); the checker also computes r_ship, the radius of check_three_level.py's docstring, built on a
         ball enclosure Z of the arc (U = Z, d = sup_Z |z - zc|, Y = sup of |Im| over Z and zc, L = sup_Z |S'|,
         m_S = inf_Z |S|), re-implemented here, and uses r = max(r_mine, r_ship).  Both are valid bounds in the
         localization lemma; the larger makes every exclusion and tile-arc condition at least as hard and the crossing
         condition |w_rep-hat(zc) - sigma S(zc)| <= r easier, consistently for all leaves of the arc;
         (|S''(w)| <= (pi^2/3) e^{pi |Im w|} since S''(w) = int (2 pi i t)^2 K_t(w) dt).
   level 2 (one witness, no pinned points):
         each tile arc: Re(conj(v) S(zc)) <= 0 and, for all p on the tile arc, Re(conj(u)S(p)) - Re(conj(v)S(zc)) - |v| r >
         tau max(0, max_t phi_p(t)), phi_p(t) = Re(conj(u)K_t(p)) - Re(conj(v)K_t(zc));
         w_rep = sum m_k delta_{t_k}: m_k >= 0, sum m_k <= tau, |t_k| <= 1/2; sigma >= 1; |w_rep-hat(zc) - sigma S(zc)| <= r;
         the winding number of G_{w_rep} along the tile is odd.
   level 3: R_j >= tau e^{pi |Im p_j|} for every j; the leaf boxes (closed rectangles Q_j, as stored) lie in the product
         of the squares, are pairwise interior-disjoint and have total volume prod_j (2R_j)^2 (hence they cover the
         product); each leaf is
         exclusion (v, y_1..y_m): Re(conj(v)S(zc)) >= 0 and
                tau max(0, max_t Lam(t)) < Re(conj(v)S(zc)) - |v| r + sum_j min_{Q_j} Re(conj(y_j)x),
                Lam(t) = Re(conj(v)K_t(zc)) + sum_j Re(conj(y_j)K_t(p_j));
         witness (tile, tile arcs (u,v,y_1..y_m), tau_rep >= tau, w_rep, sigma): with r' = r computed with tau_rep: each
                tile arc: Re(conj(v)S(zc)) <= 0 and for all p on it
                Re(conj(u)S(p)) - Re(conj(v)S(zc)) - |v| r' - sum_j max_{Q_j} Re(conj(y_j)x) > tau_rep max(0, max_t phi_p(t)),
                phi_p = Re(conj(u)K_t(p)) - Lam(t);  w_rep has m_k >= 0, sum <= tau_rep, |t_k| <= 1/2, sigma >= 1,
                |w_rep-hat(zc) - sigma S(zc)| <= r', w_rep-hat(p_j) in Q_j for every j; winding of G_{w_rep} odd.
         The number of stored boxes that differ from the position implied by the child order (lower-left, lower-right,
         upper-left, upper-right) is reported as a cross-check only.
By the proposition on multi-level certificates in Section 6 of the paper these give: G_mu has a zero of odd order for
every mu in A_tau, hence ess sup f*f > (int f)^2/(1-tau).

Rigour.  python-flint arb/acb balls (100 bits).  Arcs are enclosed in discs D(p(qm), V (q1-q0)/2), V >= sup |p'| on the
arc (|p'(q)| = 2 pi sqrt(a^2 sin^2 2 pi q + b^2 cos^2 2 pi q) evaluated over the q-interval); functions of
p are bounded by value-at-centre +- (Lipschitz bound) * radius, with sup_{D(pm,rho)} |S'| <= |S'(pm)| + rho (pi^2/3) e^{pi Y}
and |d/dp K_t(p)| <= pi e^{pi |Im p|};
functions of t in [-1/2,1/2] are bounded on cells [tc-dl, tc+dl] by f(tc) + dl |f'(tc)| + dl^2 M2 / 2 with
M2 = sum |c_j| (2 pi |zeta_j|)^2 e^{pi |Im zeta_j|} >= |f''|; cells and arcs are bisected adaptively up to fixed depths
(exceeding a depth rejects).  Winding: a piece of the tile is accepted when |G(pm)| > 2 L_G rho (image of the piece inside a
disc of angular half-width < 30 degrees around G(pm)), L_G = sup|S'| + sum m_k 2 pi |t_k| e^{2 pi |t_k| Y}; the increment is
Arg(G(p(q1))/G(p(q0))); the sum / (2 pi) must lie within 1/4 of an integer.  The "smallest tau-headroom" line of the
output is bookkeeping of the adaptive subdivision (a piece is accepted as soon as its bound clears the target) and does
not affect acceptance.

Usage: python3 -I indep_three_level.py CERT.json[.gz] NPROC [--sample K] [--only i,j,...] [--out results.jsonl]
       (the master parses the certificate once, runs the global checks and writes one chunk file per worker, with the
       global data and that worker's arcs, into RESULTS.parts; the workers are subprocesses; the results file and
       RESULTS.parts are written where --out points, by default indep3_results.jsonl in the current directory)
"""
import json, sys, os, subprocess, time, random
from fractions import Fraction
import flint
from flint import arb, acb, fmpq

flint.ctx.prec = 100
PI = arb.pi()
MAXDEPTH_ARC = 8          # bisections of an E arc
MAXDEPTH_TILE = 7         # bisections of a tile arc
MIN_TCELL = Fraction(1, 2 ** 24)
NT0 = 16                  # initial number of t-cells on [-1/2, 1/2]
STATS = {"tcells": 0, "wpieces": 0}
MARG = {}                 # bookkeeping only: smallest tau-headroom seen per condition type (does not affect acceptance)


def note_headroom(kind, A_low, maxb, dP, tau_used):
    """estimated tau-headroom of an accepted inequality tau_used * max(0, max_t f + dP) < A_low:  A_low/(fmax + dP) - tau_used,
    with fmax = largest value of f at the centres of the accepted t-cells (an estimate of max_t f; reporting only)"""
    maxb = STATS["fmax"] if STATS.get("fmax") is not None else maxb
    den = float((maxb + dP).mid())
    h = float(A_low.lower()) / den - float(tau_used) if den > 0 else 1e9
    if h < MARG.get(kind, 1e9):
        MARG[kind] = h


class Reject(Exception):
    pass


def ar(q):
    """exact arb of a Fraction"""
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def cplx(xy):
    return acb(ar(xy[0]), ar(xy[1]))


def conj_c(xy):
    return acb(ar(xy[0]), -ar(xy[1]))


def absq(xy):
    """|x + iy| as an arb ball"""
    return (ar(xy[0]) ** 2 + ar(xy[1]) ** 2).sqrt()


def up(x):
    """upper endpoint (exact arb) of a real ball"""
    return arb(x.upper())


def lo(x):
    return arb(x.lower())


def ell_pt(e, q):
    cr, ci, a, b = e
    x = ar(2 * Fraction(q))
    return acb(ar(cr) + ar(a) * x.cos_pi(), ar(ci) + ar(b) * x.sin_pi())


def ell_speed(e, q0, q1):
    """upper bound of |p'(q)| = 2 pi sqrt(a^2 sin^2(2 pi q) + b^2 cos^2(2 pi q)) for q in [q0, q1]"""
    a, b = ar(e[2]), ar(e[3])
    qq = ar(Fraction(q0)).union(ar(Fraction(q1)))
    sn, cs = (2 * qq).sin_pi(), (2 * qq).cos_pi()
    v2 = a * a * sn * sn + b * b * cs * cs
    return up(2 * PI * arb(v2.upper()).sqrt())


def ell_rad(e, q0, q1):
    """radius of a closed disc around p((q0+q1)/2) containing the arc p([q0,q1])  (mean value theorem)"""
    return up(ell_speed(e, q0, q1) * ar(Fraction(q1) - Fraction(q0)) / 2)


def Sv(z):
    w = PI * z
    return w.sin() / w


def Kv(t, z):
    return (acb(0, -2) * PI * t * z).exp()


def dSv(z):
    w = PI * z
    return (w * w.cos() - w.sin()) / (PI * z * z)


def LS_loc(zm, rho):
    """sup of |S'| on the closed disc D(zm, rho):  |S'(zm)| + rho * sup|S''|,  |S''(w)| <= (pi^2/3) e^{pi |Im w|}
    (from S''(w) = int (2 pi i t)^2 K_t(w) dt)."""
    Y = imabs_up(zm) + rho
    return up(abs(dSv(zm)) + rho * PI * PI / 3 * (PI * Y).exp())


def L_S(Y):
    """sup of |S'(w)| over |Im w| <= Y (Y > 0 exact):  int_{-1/2}^{1/2} 2 pi |t| e^{2 pi |t| Y} dt"""
    pY = PI * Y
    return up(pY.sinh() / Y - (pY.cosh() - 1) / (PI * Y * Y))


def imabs_up(z):
    return up(abs(z.imag))


def abs_up(z):
    return up(abs(z))


# ------------------------------------------------------------------ bounds in t
def t_bound_ok(terms, target):
    """Verify  f(t) := sum_j Re(c_j K_t(zeta_j)) < target  for all t in [-1/2, 1/2].
    terms: list of (c_j acb, zeta_j acb); target: arb.  Centred second-order bound on adaptive cells."""
    M2 = arb(0)
    pre = []
    for c, zt in terms:
        M2 += abs_up(c) * (2 * PI * abs_up(zt)) ** 2 * (PI * imabs_up(zt)).exp()
        pre.append((c, zt, c * acb(0, -2) * PI * zt))
    M2 = up(M2)
    stack = [(Fraction(-1, 2) + Fraction(2 * k + 1, 2 * NT0), Fraction(1, 2 * NT0)) for k in range(NT0)]
    STATS["maxb"] = None
    STATS["fmax"] = None
    while stack:
        tc, dl = stack.pop()
        STATS["tcells"] += 1
        tca = ar(tc)
        f = arb(0)
        fp = arb(0)
        for c, zt, cd in pre:
            k = Kv(tca, zt)
            f += (c * k).real
            fp += (cd * k).real
        dla = ar(dl)
        bound = f + dla * abs(fp) + dla * dla * M2 / 2
        if bound < target:
            if STATS["maxb"] is None or bound.upper() > STATS["maxb"].upper():
                STATS["maxb"] = bound
            if STATS["fmax"] is None or f.mid() > STATS["fmax"].mid():
                STATS["fmax"] = f
            continue
        if dl <= MIN_TCELL:
            return False
        h = dl / 2
        stack += [(tc - h, h), (tc + h, h)]
    return True


# ------------------------------------------------------------------ E arcs
def check_E(T1, tau, s0, s1, u, depth=0):
    sm = (s0 + s1) / 2
    z = ell_pt(T1, sm)
    rho = ell_rad(T1, s0, s1)
    Y = imabs_up(z) + rho
    uc = conj_c(u)
    ua = up(absq(u))
    A_low = lo((uc * Sv(z)).real - ua * rho * LS_loc(z, rho))
    dP = up(ua * rho * PI * (PI * Y).exp())
    if A_low > 0 and t_bound_ok([(uc, z)], A_low / ar(tau) - dP):
        note_headroom("E", A_low, STATS["maxb"], dP, tau)
        return True
    if depth >= MAXDEPTH_ARC:
        return False
    return check_E(T1, tau, s0, sm, u, depth + 1) and check_E(T1, tau, sm, s1, u, depth + 1)


# ------------------------------------------------------------------ crossing radius
def r_bound(T1, tau, s0, s1, sc):
    """r = max(r_mine, r_ship), both valid upper bounds of |w-hat(zc) - sigma S(zc)| for the relevant w;
    r_mine = the disc construction below, r_ship = the formula of check_three_level.py's docstring (ball enclosure Z of
    the arc), re-implemented here. Using the larger valid bound makes every leaf condition at least as hard and the crossing
    condition easier, consistently for all leaves of the arc."""
    rm = r_bound_mine(T1, tau, s0, s1, sc)
    rs = r_bound_ship(T1, tau, s0, s1, sc)
    return rm if rm > rs else rs


def r_bound_ship(T1, tau, s0, s1, sc):
    cr, ci, a, b = T1
    s = ar(Fraction(s0)).union(ar(Fraction(s1)))
    Z = acb(ar(cr) + ar(a) * (2 * s).cos_pi(), ar(ci) + ar(b) * (2 * s).sin_pi())
    zc = ell_pt(T1, sc)
    d = arb((Z - zc).abs_upper())
    Y = arb(max(Z.imag.abs_upper(), zc.imag.abs_upper()))
    Smin = Sv(Z).abs_lower()
    if not (Smin > 0):
        raise Reject("S vanishes on the arc enclosure (r_ship)")
    eY = (PI * Y).exp()
    smax = ar(tau) * eY / Smin
    return up(d * (ar(tau) * PI * eY + smax * arb(dSv(Z).abs_upper())))


def r_bound_mine(T1, tau, s0, s1, sc):
    a, b = T1[2], T1[3]
    zc = ell_pt(T1, sc)
    Dl = max(s1 - sc, sc - s0)
    d = up(ell_speed(T1, s0, s1) * ar(Dl))      # >= |z(s) - zc| on the arc (mean value theorem)
    Y = imabs_up(zc) + d
    L = LS_loc(zc, d)                       # sup |S'| on U = D(zc, d)
    mS = lo(abs(Sv(zc)) - d * L)
    if not (mS > 0):
        raise Reject("m_S not positive (S too small near the arc)")
    eY = (PI * Y).exp()
    sigmax = ar(tau) * eY / mS
    return up(d * (PI * ar(tau) * eY + sigmax * L))


# ------------------------------------------------------------------ boxes
def box_lin(y, Q):
    """(min, max) over x in Q = (x0,x1,y0,y1) of Re(conj(y) x) = yr xr + yi xi  (exact rationals)."""
    x0, x1, y0, y1 = Q
    yr, yi = y
    mn = (yr * x0 if yr >= 0 else yr * x1) + (yi * y0 if yi >= 0 else yi * y1)
    mx = (yr * x1 if yr >= 0 else yr * x0) + (yi * y1 if yi >= 0 else yi * y0)
    return mn, mx


# ------------------------------------------------------------------ witness tile arcs (levels 2 and 3)
def check_tile_arc(tile, q0, q1, zc, Sc, r, u, v, ypairs, hi_y, tau_w, depth=0):
    """ypairs: list of (y_j, p_j acb) for the pinned points (empty at level 2); hi_y = sum_j max_{Q_j} Re(conj(y_j) x)."""
    vc = conj_c(v)
    X = (vc * Sc).real
    if depth == 0 and not (X <= 0):
        return False
    qm = (q0 + q1) / 2
    p = ell_pt(tile, qm)
    rho = ell_rad(tile, q0, q1)
    Yp = imabs_up(p) + rho
    uc = conj_c(u)
    ua = up(absq(u))
    va = up(absq(v))
    A_low = lo((uc * Sv(p)).real - ua * rho * LS_loc(p, rho) - X - va * r - ar(hi_y))
    dP = up(ua * rho * PI * (PI * Yp).exp())
    terms = [(uc, p), (-vc, zc)]
    for yj, pj in ypairs:
        if yj[0] != 0 or yj[1] != 0:
            terms.append((-conj_c(yj), pj))
    if A_low > 0 and t_bound_ok(terms, A_low / ar(tau_w) - dP):
        note_headroom("W1_level3" if ypairs else "W1_level2", A_low, STATS["maxb"], dP, tau_w)
        return True
    if depth >= MAXDEPTH_TILE:
        return False
    return (check_tile_arc(tile, q0, qm, zc, Sc, r, u, v, ypairs, hi_y, tau_w, depth + 1)
            and check_tile_arc(tile, qm, q1, zc, Sc, r, u, v, ypairs, hi_y, tau_w, depth + 1))


def tile_arcs_tiling(tarcs):
    tarcs = sorted(tarcs, key=lambda a: a[0])
    if tarcs[0][0] != 0 or tarcs[-1][1] != 1:
        raise Reject("tile arcs do not cover [0,1]")
    for i, a in enumerate(tarcs):
        if not a[0] < a[1]:
            raise Reject("empty tile arc")
        if i + 1 < len(tarcs) and a[1] != tarcs[i + 1][0]:
            raise Reject("tile arcs not contiguous")
    return tarcs


# ------------------------------------------------------------------ winding number
def winding(tile, ts, ms):
    tsA = [ar(t) for t in ts]
    msA = [ar(m) for m in ms]

    def G(p):
        g = Sv(p)
        for t, m in zip(tsA, msA):
            g -= m * Kv(t, p)
        return g

    total = arb(0)
    stack = [(Fraction(k, 256), Fraction(k + 1, 256)) for k in range(256)]
    while stack:
        q0, q1 = stack.pop()
        qm = (q0 + q1) / 2
        pm = ell_pt(tile, qm)
        rho = ell_rad(tile, q0, q1)
        Y = imabs_up(pm) + rho
        LG = LS_loc(pm, rho)
        for t, m in zip(ts, ms):
            at = abs(Fraction(t))
            LG = LG + ar(m) * 2 * PI * ar(at) * (2 * PI * ar(at) * Y).exp()
        gm = G(pm)
        STATS["wpieces"] += 1
        if gm.abs_lower() > 2 * up(LG) * rho:
            total += (G(ell_pt(tile, q1)) / G(ell_pt(tile, q0))).arg()
            continue
        if q1 - q0 < Fraction(1, 2 ** 30):
            raise Reject("winding: piece too small")
        stack += [(q0, qm), (qm, q1)]
    wn = total / (2 * PI)
    n = int(round(float(wn.mid())))
    if not (abs(wn - n) < arb(1) / 4):
        raise Reject("winding not resolved")
    return n


def check_wrep(ts, ms, sigma, tau_w, zc, Sc, r, pcs=(), Qs=()):
    if any(m < 0 for m in ms) or sum(ms) > tau_w:
        raise Reject("w_rep: negative mass or total mass > tau_rep")
    if any(abs(t) > Fraction(1, 2) for t in ts):
        raise Reject("w_rep: atom outside [-1/2,1/2]")
    if sigma < 1:
        raise Reject("w_rep: sigma < 1")
    wc = acb(0)
    for t, m in zip(ts, ms):
        wc += ar(m) * Kv(ar(t), zc)
    if not (abs(wc - ar(sigma) * Sc) <= r):
        raise Reject("w_rep: crossing disc violated")
    for pc, Q in zip(pcs, Qs):
        wp = acb(0)
        for t, m in zip(ts, ms):
            wp += ar(m) * Kv(ar(t), pc)
        x0, x1, y0, y1 = Q
        if not (wp.real >= ar(x0) and wp.real <= ar(x1) and wp.imag >= ar(y0) and wp.imag <= ar(y1)):
            raise Reject("w_rep-hat(p_j) not certainly in its leaf box")


# ------------------------------------------------------------------ arcs
def check_H(G, arc):
    T1, tau = G["T1"], G["tau"]
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        raise Reject("sc outside arc")
    tile = G["tiles"][arc["tile"]]
    zc = ell_pt(T1, sc)
    Sc = Sv(zc)
    r = r_bound(T1, tau, s0, s1, sc)
    tarcs = tile_arcs_tiling([tuple(Fraction(x) for x in a) for a in arc["tile_arcs"]])
    for a in tarcs:
        if len(a) != 6:
            raise Reject("level-2 tile arc must have 6 entries")
        q0, q1, ur, ui, vr, vi = a
        if not check_tile_arc(tile, q0, q1, zc, Sc, r, (ur, ui), (vr, vi), [], 0, tau):
            raise Reject(f"W1 fails on tile arc [{q0},{q1}]")
    ts = [Fraction(t) for t in arc["wrep_t"]]
    ms = [Fraction(m) for m in arc["wrep_m"]]
    check_wrep(ts, ms, Fraction(arc["sigma"]), tau, zc, Sc, r)
    n = winding(tile, ts, ms)
    if n % 2 == 0:
        raise Reject(f"winding {n} even")
    return {"n": n}


def parse_tree(arc):
    """Return (points, radii, leaves) with leaves = list of (boxes tuple-of-m-boxes, leaf dict) for both formats, plus the
    number of stored boxes that differ from the position implied by the documented child order (cross-check only)."""
    if "pcs" in arc:
        pts = [(Fraction(a), Fraction(b)) for a, b in arc["pcs"]]
        Rs = [Fraction(x) for x in arc["Rs"]]
        if len(Rs) != len(pts) or not pts:
            raise Reject("pcs/Rs mismatch")
        m = len(pts)
        leaves, mism = [], [0]

        def walk(node, Qs):
            if "split" in node:
                k = node["split"]
                kids = node.get("kids")
                if not isinstance(k, int) or not (0 <= k < m) or kids is None or len(kids) != 4:
                    raise Reject("bad split node")
                x0, x1, y0, y1 = Qs[k]
                mx, my = (x0 + x1) / 2, (y0 + y1) / 2
                for kid, q in zip(kids, [(x0, mx, y0, my), (mx, x1, y0, my), (x0, mx, my, y1), (mx, x1, my, y1)]):
                    Q2 = list(Qs); Q2[k] = q
                    walk(kid, Q2)
                return
            boxes = [tuple(Fraction(x) for x in bx) for bx in node["boxes"]]
            if len(boxes) != m:
                raise Reject("leaf with wrong number of boxes")
            if boxes != list(Qs):
                mism[0] += 1
            leaves.append((tuple(boxes), node))
        walk(arc["tree"], [(-R, R, -R, R) for R in Rs])
        return pts, Rs, leaves, mism[0]
    pts = [(Fraction(arc["pc"][0]), Fraction(arc["pc"][1]))]
    Rs = [Fraction(arc["R"])]
    R = Rs[0]
    leaves, mism = [], [0]

    def walk1(node, Q):
        if "split" in node:
            kids = node["split"]
            if not isinstance(kids, list) or len(kids) != 4:
                raise Reject("split node without 4 children")
            x0, x1, y0, y1 = Q
            mx, my = (x0 + x1) / 2, (y0 + y1) / 2
            for kid, q in zip(kids, [(x0, mx, y0, my), (mx, x1, y0, my), (x0, mx, my, y1), (mx, x1, my, y1)]):
                walk1(kid, q)
            return
        box = tuple(Fraction(x) for x in node["box"])
        if box != Q:
            mism[0] += 1
        leaves.append(((box,), node))
    walk1(arc["tree"], (-R, R, -R, R))
    return pts, Rs, leaves, mism[0]


def check_cover(leaf_boxes, Rs):
    """closed product boxes inside prod_j [-R_j,R_j]^2, pairwise interior-disjoint, total volume prod (2R_j)^2
    => their union is the whole product of squares."""
    vol = Fraction(0)
    for boxes in leaf_boxes:
        v = Fraction(1)
        for (x0, x1, y0, y1), R in zip(boxes, Rs):
            if not (-R <= x0 < x1 <= R and -R <= y0 < y1 <= R):
                raise Reject("leaf box degenerate or outside the square")
            v *= (x1 - x0) * (y1 - y0)
        vol += v
    full = Fraction(1)
    for R in Rs:
        full *= (2 * R) ** 2
    if vol != full:
        raise Reject("leaf boxes do not have total volume prod (2R_j)^2")
    n = len(leaf_boxes)
    for i in range(n):
        a = leaf_boxes[i]
        for j in range(i + 1, n):
            b = leaf_boxes[j]
            overlap = True
            for qa, qb in zip(a, b):
                if not (min(qa[1], qb[1]) > max(qa[0], qb[0]) and min(qa[3], qb[3]) > max(qa[2], qb[2])):
                    overlap = False
                    break
            if overlap:
                raise Reject("leaf boxes overlap")


def check_H3(G, arc):
    T1, tau = G["T1"], G["tau"]
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        raise Reject("sc outside arc")
    zc = ell_pt(T1, sc)
    Sc = Sv(zc)
    r = r_bound(T1, tau, s0, s1, sc)
    pts, Rs, leaves, mism = parse_tree(arc)
    pcs = [cplx(q) for q in pts]
    for q, R in zip(pts, Rs):
        if not (ar(R) >= ar(tau) * (PI * ar(abs(q[1]))).exp()):
            raise Reject("R_j < tau exp(pi |Im p_j|)")
    check_cover([b for b, _ in leaves], Rs)
    m = len(pts)
    out = {"leaves": len(leaves), "empty": 0, "W": 0, "box_order_mismatch": mism, "wind": [], "points": m}
    rcache = {}
    for Qs, lf in leaves:
        typ = lf["type"]
        if typ == "empty":
            v = (Fraction(lf["v"][0]), Fraction(lf["v"][1]))
            yraw = lf["y"]
            ys = [(Fraction(yraw[0]), Fraction(yraw[1]))] if (m == 1 and not isinstance(yraw[0], list)) else \
                 [(Fraction(a), Fraction(b)) for a, b in yraw]
            if len(ys) != m:
                raise Reject("exclusion leaf with wrong number of multipliers")
            vc = conj_c(v)
            X = (vc * Sc).real
            if not (X >= 0):
                raise Reject(f"exclusion leaf {Qs}: Re(conj(v)S(zc)) not >= 0")
            mn = sum(box_lin(y, Q)[0] for y, Q in zip(ys, Qs))
            Lb = lo(X - up(absq(v)) * r + ar(mn))
            if not (Lb > 0):
                raise Reject(f"exclusion leaf {Qs}: right side not > 0")
            terms = [(vc, zc)] + [(conj_c(y), pc) for y, pc in zip(ys, pcs) if y != (0, 0)]
            if not t_bound_ok(terms, Lb / ar(tau)):
                raise Reject(f"exclusion leaf {Qs} fails")
            note_headroom("exclusion", Lb, STATS["maxb"], arb(0), tau)
            out["empty"] += 1
            continue
        if typ != "W":
            raise Reject("unknown leaf type")
        tile = G["tiles"][lf["tile"]]
        tau_w = Fraction(lf.get("tau_rep", str(tau)))
        if tau_w < tau:
            raise Reject("tau_rep < tau")
        if tau_w not in rcache:
            rcache[tau_w] = r_bound(T1, tau_w, s0, s1, sc)
        rw = rcache[tau_w]
        tarcs = tile_arcs_tiling([tuple(Fraction(x) for x in a) for a in lf["tile_arcs"]])
        for a in tarcs:
            if len(a) != 6 + 2 * m:
                raise Reject("level-3 tile arc must have 6 + 2m entries")
            q0, q1, ur, ui, vr, vi = a[:6]
            ys = [(a[6 + 2 * j], a[7 + 2 * j]) for j in range(m)]
            mx = sum(box_lin(y, Q)[1] for y, Q in zip(ys, Qs))
            if not check_tile_arc(tile, q0, q1, zc, Sc, rw, (ur, ui), (vr, vi), list(zip(ys, pcs)), mx, tau_w):
                raise Reject(f"W1 (level 3) fails on tile arc [{q0},{q1}] in leaf {Qs}")
        ts = [Fraction(t) for t in lf["wrep_t"]]
        ms = [Fraction(x) for x in lf["wrep_m"]]
        check_wrep(ts, ms, Fraction(lf["sigma"]), tau_w, zc, Sc, rw, pcs, Qs)
        n = winding(tile, ts, ms)
        if n % 2 == 0:
            raise Reject(f"winding {n} even in leaf {Qs}")
        out["W"] += 1
        out["wind"].append(n)
    return out


def check_arc(G, arc):
    typ = arc["type"]
    if typ == "E":
        if not check_E(G["T1"], G["tau"], Fraction(arc["s0"]), Fraction(arc["s1"]), (Fraction(arc["u"][0]), Fraction(arc["u"][1]))):
            raise Reject("E condition fails")
        return {}
    if typ == "H":
        return check_H(G, arc)
    if typ == "H3":
        return check_H3(G, arc)
    raise Reject("unknown arc type")


# ------------------------------------------------------------------ global structure
def load_global(path):
    if path.endswith(".gz"):
        import gzip
        with gzip.open(path, "rt") as fh:
            C = json.load(fh)
    else:
        C = json.load(open(path))
    if C.get("variant") != "Cp":
        raise SystemExit("not a one-sided (Cp) certificate")
    tau = Fraction(C["tau"])
    if not (0 < tau < 1):
        raise SystemExit("tau not in (0,1)")
    c, a, b = (Fraction(x) for x in C["T1"])
    if not (a > 0 and b > 0):
        raise SystemExit("T1 semi-axes must be positive")
    lo_, hi_ = c - a, c + a
    n_lo = lo_.__floor__() + 1                       # smallest integer > c - a
    n_hi = -((-hi_).__floor__()) - 1                 # largest integer < c + a
    zeros_inside = [n for n in range(n_lo, n_hi + 1) if n != 0]
    if len(zeros_inside) != 1:
        raise SystemExit(f"T1 must enclose exactly one zero of S; it encloses {zeros_inside}")
    for e in (lo_, hi_):
        if e.denominator == 1 and e != 0:
            raise SystemExit("T1 passes through a zero of S")
    tiles = {}
    for k, tl in C["tiles"].items():
        cr, ci, ta, tb = (Fraction(x) for x in tl)
        if not (ta > 0 and tb > 0):
            raise SystemExit(f"tile {k}: semi-axes must be positive")
        tiles[k] = (cr, ci, ta, tb)
    arcs = sorted(C["arcs"], key=lambda x: Fraction(x["s0"]))
    if Fraction(arcs[0]["s0"]) != 0 or Fraction(arcs[-1]["s1"]) != 1:
        raise SystemExit("T1 arcs do not cover [0,1]")
    for i, ac in enumerate(arcs):
        if not Fraction(ac["s0"]) < Fraction(ac["s1"]):
            raise SystemExit("empty T1 arc")
        if i + 1 < len(arcs) and Fraction(ac["s1"]) != Fraction(arcs[i + 1]["s0"]):
            raise SystemExit("T1 arcs not contiguous")
        if ac["type"] not in ("E", "H", "H3"):
            raise SystemExit("unknown arc type")
    G = {"tau": tau, "T1": (c, Fraction(0), a, b), "tiles": tiles}
    info = {"tau": str(tau), "T1": [str(c), str(a), str(b)], "zeros_inside_T1": zeros_inside,
            "tiles_zeros": {k: [n for n in range(-20, 21) if n != 0 and ((n - t[0]) / t[2]) ** 2 + (t[1] / t[3]) ** 2 < 1]
                            for k, t in tiles.items()}}
    return C, G, arcs, info


def worker(chunk_file, outfile):
    """Check the arcs of one chunk.  The chunk holds the global data (already validated by the master on the full certificate)
    and only this worker's arcs, so that no worker has to parse the whole certificate (memory)."""
    ch = json.load(open(chunk_file))
    g = ch["G"]
    G = {"tau": Fraction(g["tau"]), "T1": tuple(Fraction(x) for x in g["T1"]),
         "tiles": {k: tuple(Fraction(x) for x in t) for k, t in g["tiles"].items()}}
    with open(outfile, "w") as fo:
        for i, arc in ch["items"]:
            t0 = time.time()
            STATS["tcells"] = 0; STATS["wpieces"] = 0
            MARG.clear()
            try:
                res = check_arc(G, arc)
                ok, msg = True, ""
            except Reject as ex:
                ok, msg, res = False, str(ex), {}
            rec = {"i": i, "s0": arc["s0"], "type": arc["type"], "ok": ok, "msg": msg, "res": res,
                   "tcells": STATS["tcells"], "wpieces": STATS["wpieces"], "sec": round(time.time() - t0, 3),
                   "headroom": dict(MARG)}
            fo.write(json.dumps(rec) + "\n")
            fo.flush()


def main():
    if len(sys.argv) >= 2 and sys.argv[1] == "--worker":
        worker(sys.argv[2], sys.argv[3])
        return
    path = sys.argv[1]
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    C, G, arcs, info = load_global(path)
    print("global checks OK:", json.dumps(info), flush=True)
    idx = list(range(len(arcs)))
    if "--sample" in sys.argv:
        k = int(sys.argv[sys.argv.index("--sample") + 1])
        random.seed(12345)
        idx = sorted(random.sample(idx, k))
    if "--only" in sys.argv:
        idx = [int(x) for x in sys.argv[sys.argv.index("--only") + 1].split(",")]
    outname = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else "indep3_results.jsonl"
    workdir = os.path.abspath(outname + ".parts")
    os.makedirs(workdir, exist_ok=True)
    # spread expensive H3 arcs evenly
    gser = {"tau": str(G["tau"]), "T1": [str(x) for x in G["T1"]],
            "tiles": {k: [str(x) for x in t] for k, t in G["tiles"].items()}}
    procs = []
    for j in range(nproc):
        part = idx[j::nproc]
        if not part:
            continue
        cf = os.path.join(workdir, f"chunk_{j}.json")
        json.dump({"G": gser, "items": [[i, arcs[i]] for i in part]}, open(cf, "w"))
        of = os.path.join(workdir, f"res_{j}.jsonl")
        procs.append(subprocess.Popen([sys.executable, "-I", os.path.abspath(__file__), "--worker", cf, of]))
    del C
    t0 = time.time()
    for p in procs:
        p.wait()
    recs = []
    for j in range(nproc):
        of = os.path.join(workdir, f"res_{j}.jsonl")
        if os.path.exists(of):
            recs += [json.loads(l) for l in open(of)]
    recs.sort(key=lambda r: r["i"])
    with open(outname, "w") as fo:
        for r in recs:
            fo.write(json.dumps(r) + "\n")
    seen = {r["i"] for r in recs}
    missing = [i for i in idx if i not in seen]
    bad = [r for r in recs if not r["ok"]]
    nE = sum(1 for r in recs if r["type"] == "E"); nH = sum(1 for r in recs if r["type"] == "H")
    nH3 = sum(1 for r in recs if r["type"] == "H3")
    nleaf = sum(r["res"].get("leaves", 0) for r in recs); nemp = sum(r["res"].get("empty", 0) for r in recs)
    nW = sum(r["res"].get("W", 0) for r in recs)
    mism = sum(r["res"].get("box_order_mismatch", 0) for r in recs)
    winds = {}
    for r in recs:
        for n in r["res"].get("wind", []) + ([r["res"]["n"]] if "n" in r["res"] else []):
            winds[n] = winds.get(n, 0) + 1
    hmin = {}
    for r in recs:
        for k, v in r.get("headroom", {}).items():
            if v < hmin.get(k, (1e9, None))[0]:
                hmin[k] = (v, r["i"])
    print("smallest tau-headroom per condition (value, arc index):", {k: (round(v[0], 7), v[1]) for k, v in hmin.items()}, flush=True)
    print(f"checked {len(recs)} of {len(idx)} arcs ({nE} E, {nH} H, {nH3} H3; level-3 leaves {nleaf}: {nemp} exclusion, {nW} witness;"
          f" stored-box/tree-order mismatches {mism}); windings {winds}; wall {time.time()-t0:.0f}s", flush=True)
    if missing:
        print(f"FAILED: {len(missing)} arcs produced no result (worker crash?), first {missing[:5]}")
        sys.exit(2)
    if bad:
        print(f"FAILED: {len(bad)} arcs rejected; first: {bad[0]['i']} s0={bad[0]['s0']} {bad[0]['type']}: {bad[0]['msg']}")
        sys.exit(1)
    tau = Fraction(info["tau"])
    full = len(idx) == len(arcs)
    print(("OK (FULL)" if full else "OK (PARTIAL: subset only)") +
          f": all conditions verified; tau = {tau}; => ess sup f*f > {1/(1-tau)} (int f)^2 = {float(1/(1-tau)):.10f} (int f)^2")


if __name__ == "__main__":
    main()
