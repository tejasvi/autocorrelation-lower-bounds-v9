#!/usr/bin/env python3
"""Checker for three-level certificates with pinned points, one-sided case (signed third autocorrelation problem).

Definitions (Section 6 of the paper): S(z) = sin(pi z)/(pi z), K_t(z) = exp(-2 pi i t z), A_tau = {nonnegative measures w
on [-1/2,1/2] with int w <= tau}, G_w = S - w-hat with w-hat(z) = int K_t(z) dw(t).  T1: ellipse z(s) = c + a cos(2 pi s)
+ i b sin(2 pi s), c real, enclosing exactly one zero of S.  Arcs [s0,s1] tile [0,1]; for an H or H3 arc, zc = z(sc) and
r = r(tau) is the bound computed HERE: r = d (tau pi e^{pi Y} + sigma_max |S'|_max), d >= |z - zc| on the arc's
enclosure, Y >= |Im| there, sigma_max = tau e^{pi Y} / (lower bound of |S| on the arc's enclosure), |S'|_max on the
arc's enclosure.
  E arc (u): for all z on the arc and t in [-1/2,1/2]: Re(conj(u)S(z)) > 0 and Re(conj(u)(S(z) - tau K_t(z))) > 0.
  H arc (sc, tile, tile arcs (q0,q1,u,v), w_rep, sigma):
    for every tile arc: Re(conj(v)S(zc)) <= 0 and for all p on it, all t:
         Re(conj(u)S(p)) - Re(conj(v)S(zc)) - |v| r > tau * max(0, Re(conj(u)K_t(p)) - Re(conj(v)K_t(zc)));
    w_rep = sum m_k delta_{t_k}: m_k >= 0, sum m_k <= tau, t_k in [-1/2,1/2], sigma >= 1, |w_rep-hat(zc) - sigma S(zc)| <= r;
    the winding number of G_{w_rep} along the tile (counterclockwise) is odd (computed here).
  H3 arc (sc, points p_1..p_m ("pcs"), radii R_1..R_m ("Rs"), tree over the product of the squares [-R_j,R_j]^2 for the
    values x_j = w-hat(p_j)): R_j >= tau e^{pi |Im p_j|}, so that |w-hat(p_j)| <= R_j for every w in A_tau; a split node
    {"split": k, "kids": [4 nodes]} divides the k-th square into four equal squares (order: lower-left, lower-right,
    upper-left, upper-right); the boxes Q_1..Q_m stored in every leaf equal those of its position in the tree; each leaf is
    'empty' (v, y_1..y_m):  Re(conj(v)S(zc)) >= 0 and for all t:
         tau max(0, Re(conj(v)K_t(zc)) + sum_j Re(conj(y_j)K_t(p_j)))
              < Re(conj(v)S(zc)) - |v| r + sum_j min_{x in Q_j} Re(conj(y_j) x);
    'W' (tile, tile arcs (q0,q1,u,v,y_1..y_m), w_rep, sigma, tau_rep >= tau): with r_rep = r(tau_rep), for every tile arc
         Re(conj(v)S(zc)) <= 0 and, for all p on it and all t,
         Re(conj(u)S(p)) - Re(conj(v)S(zc)) - |v| r_rep - sum_j max_{x in Q_j} Re(conj(y_j)x)
              > tau_rep max(0, Re(conj(u)K_t(p)) - Re(conj(v)K_t(zc)) - sum_j Re(conj(y_j)K_t(p_j)));
         w_rep = sum m_k delta_{t_k} with m_k >= 0, sum m_k <= tau_rep, t_k in [-1/2,1/2], sigma >= 1,
         |w_rep-hat(zc) - sigma S(zc)| <= r_rep, w_rep-hat(p_j) in Q_j for every j, and the winding number of G_{w_rep}
         along the tile is odd.
These are the conditions of the certificate definition in Section 6 of the paper (level 1: E arcs; level 2: H arcs;
level 3: H3 arcs with m pinned points).  Consequence: for every real f in L^1 supported on [-1/4,1/4] with
int f != 0, ess sup f*f > (int f)^2/(1-tau).  In the output, C and C' are the paper's C_3 and C_3'.
Usage: python3 -I check_three_level.py cert.json[.gz] [nproc]
"""
import json, sys, itertools
from fractions import Fraction
from multiprocessing import Pool
import flint
from flint import arb, acb, fmpq
if not __debug__:
    raise SystemExit("this checker relies on assert statements; run it without -O")

flint.ctx.prec = 80
G = {}
PI = arb.pi()
II = acb(0, 1)

def A(q):
    return arb(fmpq(q.numerator, q.denominator))

def hull(q0, q1):
    return A(q0).union(A(q1))

def ell_ball(e, s0, s1):
    cr, ci, a, b = e
    s = hull(s0, s1)
    return acb(A(cr) + A(a) * (2 * s).cos_pi(), A(ci) + A(b) * (2 * s).sin_pi())

def S(z):
    return (PI * z).sin() / (PI * z)

def dS(z):
    return (PI * z * (PI * z).cos() - (PI * z).sin()) / (PI * z * z)

def K(t, z):
    return (-2 * PI * II * t * z).exp()

def check_E(s0, s1, u, depth=0):
    tau = A(G["tau"])
    z = ell_ball(G["T1"], s0, s1)
    uc = acb(A(u[0]), -A(u[1]))
    Sz = S(z)
    ok = bool((uc * Sz).real > 0)
    if ok:
        stack = [(Fraction(-1, 2), Fraction(1, 2), 0)]
        while stack:
            t0, t1, d = stack.pop()
            if (uc * (Sz - tau * K(hull(t0, t1), z))).real > 0:
                continue
            if d >= 22:
                ok = False
                break
            m = (t0 + t1) / 2
            stack += [(t0, m, d + 1), (m, t1, d + 1)]
    if ok:
        return True
    if depth >= 4:
        return False
    m = (s0 + s1) / 2
    return check_E(s0, m, u, depth + 1) and check_E(m, s1, u, depth + 1)

def r_bound(s0, s1, sc, tau_val=None):
    tau = A(G["tau"] if tau_val is None else tau_val)
    Z = ell_ball(G["T1"], s0, s1)
    zc = ell_ball(G["T1"], sc, sc)
    d = arb((Z - zc).abs_upper())
    Y = arb(max(Z.imag.abs_upper(), zc.imag.abs_upper()))
    Smin = S(Z).abs_lower()
    assert Smin > 0, "S vanishes near an H arc"
    smax = tau * (PI * Y).exp() / Smin
    r = d * (tau * PI * (PI * Y).exp() + smax * arb(dS(Z).abs_upper()))
    return arb(r.upper())

def check_tile_arc(tile, q0, q1, zc, Sc, r, u, v, depth=0):
    tau = A(G["tau"])
    uc = acb(A(u[0]), -A(u[1]))
    vc = acb(A(v[0]), -A(v[1]))
    vabs = (A(v[0]) * A(v[0]) + A(v[1]) * A(v[1])).sqrt()
    X = (vc * Sc).real
    if not (X <= 0):
        return False
    P = ell_ball(tile, q0, q1)
    L = arb(((uc * S(P)).real - X - vabs * r).lower())
    ok = bool(L > 0)
    if ok:
        stack = [(Fraction(-1, 2), Fraction(1, 2), 0)]
        while stack:
            t0, t1, d = stack.pop()
            T = hull(t0, t1)
            phi = (uc * K(T, P)).real - (vc * K(T, zc)).real
            if tau * phi < L:
                continue
            if d >= 22:
                ok = False
                break
            m = (t0 + t1) / 2
            stack += [(t0, m, d + 1), (m, t1, d + 1)]
    if ok:
        return True
    if depth >= 4:
        return False
    m = (q0 + q1) / 2
    return (check_tile_arc(tile, q0, m, zc, Sc, r, u, v, depth + 1)
            and check_tile_arc(tile, m, q1, zc, Sc, r, u, v, depth + 1))

def winding(tile, ts, ms):
    tsA = [A(t) for t in ts]
    msA = [A(m) for m in ms]
    def Gf(z):
        g = S(z)
        for t, m in zip(tsA, msA):
            g -= m * K(t, z)
        return g
    total = arb(0)
    todo = [(Fraction(k, 1024), Fraction(k + 1, 1024)) for k in range(1024)]
    pieces = 0
    while todo:
        q0, q1 = todo.pop()
        B = Gf(ell_ball(tile, q0, q1))
        if B.abs_lower() > 0 and B.rad() < 0.5 * B.abs_lower():
            g0 = Gf(ell_ball(tile, q0, q0))
            g1 = Gf(ell_ball(tile, q1, q1))
            total += (g1 / g0).arg()
            pieces += 1
            continue
        if q1 - q0 < Fraction(1, 2 ** 24):
            return None
        m = (q0 + q1) / 2
        todo += [(q0, m), (m, q1)]
    w = total / (2 * PI)
    n = round(float(w.mid()))
    if not (abs(w - n) < arb(1) / 4):
        return None
    return n

def check_H(arc):
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        return "sc outside arc"
    tile = G["tiles"][arc["tile"]]
    zc = ell_ball(G["T1"], sc, sc)
    Sc = S(zc)
    r = r_bound(s0, s1, sc)
    # tile arcs tile [0,1]
    tarcs = sorted([(Fraction(a[0]), Fraction(a[1]), (Fraction(a[2]), Fraction(a[3])), (Fraction(a[4]), Fraction(a[5])))
                    for a in arc["tile_arcs"]], key=lambda x: x[0])
    if tarcs[0][0] != 0 or tarcs[-1][1] != 1:
        return "tile arcs do not cover [0,1]"
    for i in range(len(tarcs)):
        if not tarcs[i][0] < tarcs[i][1]:
            return "empty tile arc"
        if i + 1 < len(tarcs) and tarcs[i][1] != tarcs[i + 1][0]:
            return "tile arcs not contiguous"
    for (q0, q1, u, v) in tarcs:
        if not check_tile_arc(tile, q0, q1, zc, Sc, r, u, v):
            return f"W1 fails on tile arc [{q0},{q1}]"
    # W2
    ts = [Fraction(t) for t in arc["wrep_t"]]
    ms = [Fraction(m) for m in arc["wrep_m"]]
    sigma = Fraction(arc["sigma"])
    tau = G["tau"]
    if any(m < 0 for m in ms) or sum(ms) > tau or any(not (Fraction(-1, 2) <= t <= Fraction(1, 2)) for t in ts) or sigma < 1:
        return "W2: w_rep not admissible"
    what = acb(0)
    for t, m in zip(ts, ms):
        what += A(m) * K(A(t), zc)
    if not ((what - A(sigma) * Sc).abs_upper() <= r):
        return "W2: w_rep violates the crossing constraint"
    # W3
    n = winding(tile, ts, ms)
    if n is None or n % 2 == 0:
        return f"W3: winding {n} not odd"
    return None


def box_minmax(y, Q):
    x0, x1, y0, y1 = Q
    yr, yi = y
    lo = (A(yr) * A(x0) if yr >= 0 else A(yr) * A(x1)) + (A(yi) * A(y0) if yi >= 0 else A(yi) * A(y1))
    hi = (A(yr) * A(x1) if yr >= 0 else A(yr) * A(x0)) + (A(yi) * A(y1) if yi >= 0 else A(yi) * A(y0))
    return lo, hi

def check_empty_m(zc, pcs, Sc, r, Qs, v, ys):
    tau = A(G["tau"])
    vc = acb(A(v[0]), -A(v[1]))
    X = (vc * Sc).real
    if not (X >= 0):
        return False
    vabs = (A(v[0]) * A(v[0]) + A(v[1]) * A(v[1])).sqrt()
    lo = arb(0)
    for y, Q in zip(ys, Qs):
        lo += box_minmax(y, Q)[0]
    L = arb((X - vabs * r + lo).lower())
    if not (L > 0):
        return False
    ycs = [acb(A(y[0]), -A(y[1])) for y in ys]
    stack = [(Fraction(-1, 2), Fraction(1, 2), 0)]
    while stack:
        t0, t1, d = stack.pop()
        T = hull(t0, t1)
        phi = (vc * K(T, zc)).real
        for yc, pc in zip(ycs, pcs):
            phi += (yc * K(T, pc)).real
        if tau * phi < L:
            continue
        if d >= 22:
            return False
        m = (t0 + t1) / 2
        stack += [(t0, m, d + 1), (m, t1, d + 1)]
    return True

def check_wit_arc_m(tile, q0, q1, zc, pcs, Sc, r, Qs, u, v, ys, tau_w, depth=0):
    tau = A(tau_w)
    uc = acb(A(u[0]), -A(u[1])); vc = acb(A(v[0]), -A(v[1]))
    X = (vc * Sc).real
    if not (X <= 0):
        return False
    vabs = (A(v[0]) * A(v[0]) + A(v[1]) * A(v[1])).sqrt()
    hi = arb(0)
    for y, Q in zip(ys, Qs):
        hi += box_minmax(y, Q)[1]
    ycs = [acb(A(y[0]), -A(y[1])) for y in ys]
    P = ell_ball(tile, q0, q1)
    L = arb(((uc * S(P)).real - X - vabs * r - hi).lower())
    ok = bool(L > 0)
    if ok:
        stack = [(Fraction(-1, 2), Fraction(1, 2), 0)]
        while stack:
            t0, t1, d = stack.pop()
            T = hull(t0, t1)
            phi = (uc * K(T, P)).real - (vc * K(T, zc)).real
            for yc, pc in zip(ycs, pcs):
                phi -= (yc * K(T, pc)).real
            if tau * phi < L:
                continue
            if d >= 22:
                ok = False
                break
            m = (t0 + t1) / 2
            stack += [(t0, m, d + 1), (m, t1, d + 1)]
    if ok:
        return True
    if depth >= 4:
        return False
    m = (q0 + q1) / 2
    return (check_wit_arc_m(tile, q0, m, zc, pcs, Sc, r, Qs, u, v, ys, tau_w, depth + 1)
            and check_wit_arc_m(tile, m, q1, zc, pcs, Sc, r, Qs, u, v, ys, tau_w, depth + 1))

def leaves_of_m(node, Qs, out):
    if "split" in node:
        k = node["split"]
        x0, x1, y0, y1 = Qs[k]
        mx = (x0 + x1) / 2; my = (y0 + y1) / 2
        assert len(node["kids"]) == 4
        for kid, q in zip(node["kids"], [(x0, mx, y0, my), (mx, x1, y0, my), (x0, mx, my, y1), (mx, x1, my, y1)]):
            Q2 = list(Qs); Q2[k] = q
            leaves_of_m(kid, Q2, out)
        return
    boxes = [tuple(Fraction(b) for b in bx) for bx in node["boxes"]]
    assert boxes == list(Qs), "leaf boxes do not match their tree position"
    out.append((list(Qs), node))

def check_H3(arc):
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        return "sc outside arc"
    zc = ell_ball(G["T1"], sc, sc)
    Sc = S(zc)
    r = r_bound(s0, s1, sc)
    tau = G["tau"]
    pts = [(Fraction(a), Fraction(b)) for a, b in arc["pcs"]]
    pcs = [acb(A(a), A(b)) for a, b in pts]
    Rs = [Fraction(R) for R in arc["Rs"]]
    if len(Rs) != len(pts):
        return "Rs/pcs mismatch"
    for (a, b), R in zip(pts, Rs):
        if not (A(R) >= A(tau) * (PI * abs(A(b))).exp()):
            return "R too small"
    leaves = []
    leaves_of_m(arc["tree"], [(-R, R, -R, R) for R in Rs], leaves)
    m = len(pts)
    for Qs, lf in leaves:
        if lf["type"] == "empty":
            v = (Fraction(lf["v"][0]), Fraction(lf["v"][1])); ys = [(Fraction(a), Fraction(b)) for a, b in lf["y"]]
            if len(ys) != m or not check_empty_m(zc, pcs, Sc, r, Qs, v, ys):
                return f"empty leaf fails at boxes {Qs}"
            continue
        if lf["type"] != "W":
            return "unknown leaf type"
        tile = G["tiles"][lf["tile"]]
        tau_rep = Fraction(lf.get("tau_rep", str(tau)))
        if tau_rep < tau:
            return "W leaf: tau_rep < tau"
        r_rep = r_bound(s0, s1, sc, tau_rep)
        tarcs = []
        for a in lf["tile_arcs"]:
            if len(a) != 6 + 2 * m:
                return "W leaf: wrong tile arc length"
            tarcs.append((Fraction(a[0]), Fraction(a[1]), (Fraction(a[2]), Fraction(a[3])), (Fraction(a[4]), Fraction(a[5])),
                          [(Fraction(a[6 + 2 * j]), Fraction(a[7 + 2 * j])) for j in range(m)]))
        tarcs.sort(key=lambda x: x[0])
        if tarcs[0][0] != 0 or tarcs[-1][1] != 1:
            return "tile arcs do not cover [0,1]"
        for i in range(len(tarcs)):
            if not tarcs[i][0] < tarcs[i][1]:
                return "empty tile arc"
            if i + 1 < len(tarcs) and tarcs[i][1] != tarcs[i + 1][0]:
                return "tile arcs not contiguous"
        for (q0, q1, u, v, ys) in tarcs:
            if not check_wit_arc_m(tile, q0, q1, zc, pcs, Sc, r_rep, Qs, u, v, ys, tau_rep):
                return f"W leaf fails on tile arc [{q0},{q1}] at boxes {Qs}"
        ts = [Fraction(t) for t in lf["wrep_t"]]; ms = [Fraction(x) for x in lf["wrep_m"]]; sigma = Fraction(lf["sigma"])
        if any(x < 0 for x in ms) or sum(ms) > tau_rep or any(not (Fraction(-1, 2) <= t <= Fraction(1, 2)) for t in ts) or sigma < 1:
            return "W leaf: w_rep not admissible"
        what_c = acb(0)
        for t, x in zip(ts, ms):
            what_c += A(x) * K(A(t), zc)
        if not ((what_c - A(sigma) * Sc).abs_upper() <= r_rep):
            return "W leaf: w_rep violates the crossing constraint"
        for pc, (x0, x1, y0, y1) in zip(pcs, Qs):
            wp = acb(0)
            for t, x in zip(ts, ms):
                wp += A(x) * K(A(t), pc)
            if not (wp.real >= A(x0) and wp.real <= A(x1) and wp.imag >= A(y0) and wp.imag <= A(y1)):
                return "W leaf: w_rep-hat(p_j) not in its box"
        n = winding(tile, ts, ms)
        if n is None or n % 2 == 0:
            return f"W leaf: winding {n} not odd"
    return None

def work(item):
    kind, arc = item
    if kind == "H3":
        return check_H3(arc)
    if kind == "E":
        return None if check_E(Fraction(arc["s0"]), Fraction(arc["s1"]), (Fraction(arc["u"][0]), Fraction(arc["u"][1]))) else "E fails"
    return check_H(arc)

def init(g):
    G.update(g)

def main(path, nproc):
    if path.endswith(".gz"):
        import gzip
        with gzip.open(path, "rt") as fh:
            C = json.load(fh)
    else:
        C = json.load(open(path))
    assert C["variant"] == "Cp"
    tau = Fraction(C["tau"])
    assert 0 < tau < 1
    c, a, b = (Fraction(x) for x in C["T1"])
    assert a > 0 and b > 0
    lo, hi = c - a, c + a
    ints = [n for n in range(int(lo) - 2, int(hi) + 3) if n != 0 and lo < n < hi]
    assert len(ints) == 1, "T1 must enclose exactly one zero of S"
    assert not (lo.denominator == 1 and lo != 0) and not (hi.denominator == 1 and hi != 0)
    tiles = {}
    for key, tl in C["tiles"].items():
        cr, ci, ta, tb = (Fraction(x) for x in tl)
        assert ta > 0 and tb > 0
        tiles[key] = (cr, ci, ta, tb)
    arcs = sorted(C["arcs"], key=lambda x: Fraction(x["s0"]))
    assert Fraction(arcs[0]["s0"]) == 0 and Fraction(arcs[-1]["s1"]) == 1, "arcs must cover [0,1]"
    for i in range(len(arcs)):
        assert Fraction(arcs[i]["s0"]) < Fraction(arcs[i]["s1"])
        if i + 1 < len(arcs):
            assert Fraction(arcs[i]["s1"]) == Fraction(arcs[i + 1]["s0"]), "arcs not contiguous"
    g = {"tau": tau, "T1": (c, Fraction(0), a, b), "tiles": tiles}
    items = [(arc["type"], arc) for arc in arcs]
    assert all(k in ("E", "H", "H3") for k, _ in items)
    with Pool(nproc, initializer=init, initargs=(g,)) as pool:
        res = pool.map(work, items, chunksize=4)
    bad = [(arcs[i]["s0"], r) for i, r in enumerate(res) if r is not None]
    nE = sum(1 for k, _ in items if k == "E"); nH3 = sum(1 for k, _ in items if k == "H3"); nH = len(items) - nE - nH3
    if bad:
        print(f"FAILED: {len(bad)} of {len(items)} arcs; first: {bad[0]}")
        sys.exit(1)
    bound = 1 / (1 - tau)
    print(f"OK: three-level certificate, tau = {tau} = {float(tau)}; {nE} E arcs, {nH} H arcs, {nH3} H3 arcs verified")
    print(f"=> ess sup f*f > {bound} (int f)^2 = {float(bound):.10f} (int f)^2, so C >= C' >= {bound}")

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 8)
