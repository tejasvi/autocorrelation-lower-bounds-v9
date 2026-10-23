#!/usr/bin/env python3
"""Checker for NESTED zero-parity certificates (signed third autocorrelation, variant Cp), for the nested certificates of
Section 6 of the paper; it extends check_three_level.py to trees of nodes.

Definitions: S(z) = sin(pi z)/(pi z), K_t(z) = exp(-2 pi i t z), w-hat(z) = int w K_t(z) dt, G_w = S - w-hat,
W_tau = {w >= 0 measure on [-1/2,1/2], int w <= tau}.  T1: ellipse z(s) = c + a cos(2 pi s) + i b sin(2 pi s) (c real)
enclosing exactly one zero of S; tiles: ellipses (cr, ci, a, b), parameter q in [0,1], z(q) = cr + a cos 2 pi q + i(ci + b sin 2 pi q).

Arcs [s0,s1] of T1 tile [0,1]; each is
  E  (u): Re(conj u S(z)) > 0 and Re(conj u (S(z) - tau K_t(z))) > 0 for z on the arc, all t      (no crossing on the arc)
  H  : as an N arc whose tree is a single W leaf with no box points (fields s0, s1, sc, tile, tile_arcs, wrep_t, wrep_m, sigma)
  N/H3 (s0, s1, sc, pcs, Rs, tree): box points p_j with R_j >= tau e^{pi |Im p_j|}; tree over the product of [-R_j,R_j]^2 for
       x_j = w-hat(p_j) (split nodes {"split": j, "kids": [4]} bisect box j: lower-left, lower-right, upper-left, upper-right).
Constraint sets.  A leaf at boxes Qs with tube list Tubes and mass parameter tau_N >= tau (field "tau_rep", default tau) has
  C = {w >= 0, int w <= tau_N, exists sigma >= 1: |w-hat(zc) - sigma S(zc)| <= r_1, w-hat(p_j) in Q_j,
       exists mu_k >= 0: |w-hat(c_k) - S(c_k) - mu_k g_k| <= r_k for every tube k},
  r_1 = d (tau_N pi e^{pi Y} + sigma_max |S'|max) on the T1 arc (sigma_max = tau_N e^{pi Y}/min|S|), and for a tube made from the
  hard arc [q0,q1] of a tile with base atoms (t_i, m_i): c = z(qc), qc = (q0+q1)/2, g = G_base(c), and
  r = d (tau_N pi e^{pi Y} + D_S + mu_max D_0), mu_max = (tau_N e^{pi Y} + S_max)/m_0, all computed HERE from the arc ball P:
  d >= |z - c|, Y >= |Im P|, D_S >= |S'(P)|, D_0 >= |G_base'(P)|, S_max >= |S| and 0 < m_0 <= |G_base| on the arc.
Leaves.
  empty (v, y_j, vt_k):  Re(conj v S(zc)) >= 0, Re(conj vt_k g_k) >= 0 and for all t:
       tau_N max(0, psi(t)) < Re(conj v S(zc)) - |v| r_1 + sum_j min_{Q_j} Re(conj y_j x) + sum_k [Re(conj vt_k S(c_k)) - |vt_k| r_k],
       psi(t) = Re(conj v K_t(zc)) + sum_j Re(conj y_j K_t(p_j)) + sum_k Re(conj vt_k K_t(c_k))          => C is empty.
  W (tile, tile_arcs, wrep_t, wrep_m, sigma, mus):  the tile arcs tile [0,1]; each is
     W1 [q0, q1, ur, ui, vr, vi, y_1r, y_1i, ..., vt_1r, vt_1i, ...]:  Re(conj v S(zc)) <= 0, Re(conj vt_k g_k) <= 0 and for all
       p on the arc, all t:  Re(conj u S(p)) - Re(conj v S(zc)) - |v| r_1 - sum_j max_{Q_j} Re(conj y_j x)
                                  - sum_k [Re(conj vt_k S(c_k)) + |vt_k| r_k] > tau_N max(0, phi(t)),
       phi(t) = Re(conj u K_t(p)) - Re(conj v K_t(zc)) - sum_j Re(conj y_j K_t(p_j)) - sum_k Re(conj vt_k K_t(c_k));
     hard {"hard": [q0, q1], "child": tree}: the child tree starts at the same boxes Qs and has the tube list Tubes + [tube made
       from this arc with base w_rep of this leaf];
     w_rep = sum m_i delta_{t_i} lies in C (mass <= tau_N, crossing disc with sigma >= 1, boxes, tubes with mu_k >= 0) and the
     winding number of G_{w_rep} along the tile is odd (computed here).
Interval tubes (the tube conditions of the paper): a hard arc entry with "kind": "iv" gives the exact constraint
  exists z in A'' = z([q0,q1]), mu >= 0: |w-hat(z) - S(z) - mu G_base(z)| <= eps  (eps = certificate field "iv_eps", default 1e-9);
  node sets are convex hulls; in the leaf conditions the tube's terms are bounded uniformly over a ball Z containing the arc:
  W1: Re(conj vt G_base(Z)) <= 0, bound term sup Re(conj vt S(Z)) + |vt| eps, phi term -Re(conj vt K_t(Z)) (sup over Z);
  empty: Re(conj vt G_base(Z)) >= 0, bound term inf Re(conj vt S(Z)) - |vt| eps, psi term +Re(conj vt K_t(Z));
  w_rep gives [q_r, mu_r] (q0 <= q_r <= q1, mu_r >= 0) with |w_rep-hat(z(q_r)) - S(z(q_r)) - mu_r G_base(z(q_r))| <= eps.
ivsplit nodes {"ivsplit": k, "at": qm, "kids": [lo, hi]} (the arc splits of the paper): interval tube k (index in the node's
  tube list, root-first) has its arc [q0,q1] split at q0 < qm < q1; kid lo uses [q0,qm], kid hi uses [qm,q1] (same tile and
  base atoms, same boxes); both kids must be certified.
Consequence (Section 6 of the paper): every w in W_tau has a zero of odd multiplicity, hence for every real f
in L^1 supported on [-1/4,1/4]: ess sup f*f > (int f)^2/(1-tau).
Usage: python3 -I check_nested.py cert.json[.gz] [nproc] [--subset] [--deep]
  --subset: per-arc checks only, no coverage claim;  --deep: same conditions, the subtrees under the hard arcs of a root W
  leaf are checked as separate pool jobs (load balance for large arcs).
"""
import json, sys
from fractions import Fraction
from multiprocessing import Pool
import flint
from flint import arb, acb, fmpq

if not __debug__:                         # vC (ii): the checks use assert; python -O would skip them
    raise SystemExit("check_nested vC: refusing to run with python -O (assertions disabled)")
flint.ctx.prec = 80
G = {}
PI = arb.pi()
II = acb(0, 1)
TDEPTH = 22

def A(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))

def hull(q0, q1):
    return A(q0).union(A(q1))

def ell_ball(e, q0, q1):
    cr, ci, a, b = e
    s = hull(q0, q1)
    return acb(A(cr) + A(a) * (2 * s).cos_pi(), A(ci) + A(b) * (2 * s).sin_pi())

def S(z):
    return (PI * z).sin() / (PI * z)

def dS(z):
    return (PI * z * (PI * z).cos() - (PI * z).sin()) / (PI * z * z)

def K(t, z):
    return (-2 * PI * II * t * z).exp()

def cplx(p):
    return (Fraction(p[0]), Fraction(p[1]))

def conj_ball(p):
    return acb(A(p[0]), -A(p[1]))

def absq(p):
    return (A(p[0]) * A(p[0]) + A(p[1]) * A(p[1])).sqrt()

def G_atoms(z, ts, ms):
    g = S(z)
    for t, m in zip(ts, ms):
        g -= A(m) * K(A(t), z)
    return g

def dG_atoms(z, ts, ms):
    g = dS(z)
    for t, m in zip(ts, ms):
        g += A(m) * 2 * PI * II * A(t) * K(A(t), z)
    return g

def what_atoms(z, ts, ms):
    s = acb(0)
    for t, m in zip(ts, ms):
        s += A(m) * K(A(t), z)
    return s

# ---------------------------------------------------------------- level-1 radius
def r1_bound(s0, s1, sc, tau_N):
    tau = A(tau_N)
    Z = ell_ball(G["T1"], s0, s1)
    zc = ell_ball(G["T1"], sc, sc)
    d = arb((Z - zc).abs_upper())
    Y = arb(max(Z.imag.abs_upper(), zc.imag.abs_upper()))
    Smin = S(Z).abs_lower()
    if not (Smin > 0):
        raise ValueError("S vanishes near an H arc")
    smax = tau * (PI * Y).exp() / Smin
    return arb((d * (tau * PI * (PI * Y).exp() + smax * arb(dS(Z).abs_upper()))).upper())

# ---------------------------------------------------------------- tubes
NSUB_IV = (8, 64)
NSUB_T = 4
def iv_subballs(tube):
    """the arc of an interval tube as a union of NSUB_T arb balls (for the t-sweep terms)."""
    kind, tile, q0, q1, ts, ms = tube
    return [ell_ball(tile, q0 + (q1 - q0) * Fraction(i, NSUB_T), q0 + (q1 - q0) * Fraction(i + 1, NSUB_T)) for i in range(NSUB_T)]
def iv_bounds(tube, vt, sign, cache):
    """interval tube (kind 'iv'): rigorous (sign_ok, bound term) for multiplier vt over the arc, trying 1, 8, 64 sub-balls.
    sign = -1 (W1: need Re(conj vt G) <= 0, bound = sup Re(conj vt S) + |vt| eps) or +1 (empty: need >= 0, bound = inf ... - |vt| eps)."""
    kind, tile, q0, q1, ts, ms = tube
    vtc = conj_ball(vt); eps = A(G["iv_eps"])
    for nsub in NSUB_IV:
        ok = True; bound = None
        for i in range(nsub):
            Zi = ell_ball(tile, q0 + (q1 - q0) * Fraction(i, nsub), q0 + (q1 - q0) * Fraction(i + 1, nsub))
            sg = (vtc * G_atoms(Zi, ts, ms)).real
            if not ((sg <= 0) if sign < 0 else (sg >= 0)):
                ok = False; break
            sb = (vtc * S(Zi)).real
            if sign < 0:
                bound = arb(sb.upper()) if bound is None else arb(max(bound.upper(), sb.upper()))
            else:
                bound = arb(sb.lower()) if bound is None else arb(min(bound.lower(), sb.lower()))
        if ok:
            return True, (bound + absq(vt) * eps if sign < 0 else bound - absq(vt) * eps)
    return False, None

def tube_data(tube, tau_N, cache):
    """disc tube = ('disc', tile tuple, q0, q1, ts, ms) -> (c ball, a = S(c), g = G_base(c), r upper bound) for mass parameter tau_N."""
    kind, tile, q0, q1, ts, ms = tube
    assert kind == "disc"
    key = (kind, tile, q0, q1, tuple(ts), tuple(ms), tau_N)      # content key (never id(): freed tuples reuse ids)
    if key in cache:
        return cache[key]
    qc = (q0 + q1) / 2
    c = ell_ball(tile, qc, qc)
    P = ell_ball(tile, q0, q1)
    d = arb((P - c).abs_upper())
    Y = arb(max(P.imag.abs_upper(), c.imag.abs_upper()))
    DS = arb(dS(P).abs_upper())
    D0 = arb(dG_atoms(P, ts, ms).abs_upper())
    # m_0 and S_max over 16 sub-balls of the arc
    m0 = None; Smax = arb(0)
    for i in range(16):
        Pi = ell_ball(tile, q0 + (q1 - q0) * Fraction(i, 16), q0 + (q1 - q0) * Fraction(i + 1, 16))
        lo = arb(G_atoms(Pi, ts, ms).abs_lower())
        m0 = lo if m0 is None else arb(min(m0.lower(), lo.lower()))
        Smax = arb(max(Smax.upper(), S(Pi).abs_upper()))
    if not (m0 > 0):
        raise ValueError("base G vanishes (or is not separated from 0) on a hard arc")
    tau = A(tau_N)
    mu_max = (tau * (PI * Y).exp() + Smax) / m0
    r = arb((d * (tau * PI * (PI * Y).exp() + DS + mu_max * D0)).upper())
    out = (c, S(c), G_atoms(c, ts, ms), r)
    cache[key] = out
    return out

# ---------------------------------------------------------------- boxes
def box_minmax(y, Q):
    x0, x1, y0, y1 = Q
    yr, yi = y
    lo = (A(yr) * A(x0) if yr >= 0 else A(yr) * A(x1)) + (A(yi) * A(y0) if yi >= 0 else A(yi) * A(y1))
    hi = (A(yr) * A(x1) if yr >= 0 else A(yr) * A(x0)) + (A(yi) * A(y1) if yi >= 0 else A(yi) * A(y0))
    return lo, hi

# ---------------------------------------------------------------- t-sweep
TCELL = {}
def tcell(d, k):
    """arb ball of the dyadic t-cell [-1/2 + k/2^d, -1/2 + (k+1)/2^d] (exact rational endpoints)."""
    b = TCELL.get((d, k))
    if b is None:
        b = hull(Fraction(-1, 2) + Fraction(k, 2 ** d), Fraction(-1, 2) + Fraction(k + 1, 2 ** d))
        TCELL[(d, k)] = b
    return b

T0CELL = {}
def t_cell_center(d, k):
    v = T0CELL.get((d, k))
    if v is None:
        v = (A(Fraction(-1, 2) + Fraction(2 * k + 1, 2 ** (d + 1))), A(Fraction(1, 2 ** (d + 1))))
        T0CELL[(d, k)] = v
    return v

def t_sweep_below(terms, tau_N, L, kc=None):
    """True iff tau_N * phi(t) < L for all t in [-1/2,1/2], phi(t) = sum Re(coef * K_t(z)) over terms (coef, z[, zkey]);
    z is an acb ball (or a list of balls: z ranges over their union).  Second-order (Taylor) bound on each dyadic t-cell
    [t0 - h, t0 + h]: for every fixed choice of the z's, phi(t) <= phi(t0) + h |phi'(t0)| + (h^2/2) M2 with
    phi'(t) = sum Re(coef (-2 pi i z) K_t(z)) and M2 = sum |coef| 4 pi^2 Rz^2 e^{pi Yz} >= sup |phi''| (|t| <= 1/2,
    Rz >= |z|, Yz >= |Im z| on the term's z-set).  phi(t0), phi'(t0) are enclosed over all z (unions for list terms).
    K_{t0}(z) and z K_{t0}(z) of terms with a hashable zkey are cached in kc per (zkey id, cell) (coefficient-free values)."""
    tau = A(tau_N)
    two_pi_i = 2 * PI * II
    ids = kc.setdefault("__ids3__", {}) if kc is not None else None
    tl = []
    M2 = arb(0)
    for term in terms:
        coef, z = term[0], term[1]
        zkey = term[2] if len(term) > 2 else None
        zs = z if isinstance(z, list) else [z]
        R = max(zi.abs_upper() for zi in zs)
        Y = max(arb(zi.imag).abs_upper() for zi in zs)
        M2 += arb(abs(coef).upper()) * 4 * PI * PI * arb(R) * arb(R) * (PI * arb(Y)).exp()
        zid = ids.setdefault(zkey, len(ids)) if (zkey is not None and ids is not None) else None
        tl.append((coef, zs, zid))
    M2 = arb(M2.upper())
    stack = [(1, 0), (1, 1)]          # depth-1 cells [-1/2, 0], [0, 1/2]
    while stack:
        d, k = stack.pop()
        t0, hA = t_cell_center(d, k)
        F = arb(0); D = arb(0)
        for coef, zs, zid in tl:
            vals = kc.get(("t3", zid, d, k)) if zid is not None else None
            if vals is None:
                vals = []
                for zi in zs:
                    Kz = (-two_pi_i * t0 * zi).exp()
                    vals.append((Kz, (-two_pi_i * zi) * Kz))
                if zid is not None:
                    kc[("t3", zid, d, k)] = vals
            fv = None; dv = None
            for Kz, dKz in vals:
                f_ = (coef * Kz).real; d_ = (coef * dKz).real
                fv = f_ if fv is None else fv.union(f_)
                dv = d_ if dv is None else dv.union(d_)
            F += fv; D += dv
        B = arb(F.upper()) + hA * arb(D.abs_upper()) + hA * hA * M2 / 2
        if tau * B < L:
            continue
        if d >= TDEPTH:
            return False
        stack += [(d + 1, 2 * k), (d + 1, 2 * k + 1)]
    return True

# ---------------------------------------------------------------- leaf checks
class Ctx:
    """per-arc context: zc, Sc, T1 arc data, box points."""
    pass

def check_empty(ctx, Qs, tubes, lf, cache):
    tau_N = Fraction(lf.get("tau_rep", str(G["tau"])))
    if tau_N < G["tau"]:
        return "empty leaf: tau_rep < tau"
    r1 = r1_bound(ctx.s0, ctx.s1, ctx.sc, tau_N)
    v = cplx(lf["v"]); ys = [cplx(y) for y in lf["y"]]; vts = [cplx(x) for x in lf.get("vt", [])]
    if len(ys) != len(ctx.pcs) or len(vts) != len(tubes):
        return "empty leaf: multiplier count mismatch"
    vc = conj_ball(v)
    X = (vc * ctx.Sc).real
    if not (X >= 0):
        return "empty leaf: Re(conj v S(zc)) >= 0 fails"
    L = X - absq(v) * r1
    terms = [(vc, ctx.zc, "zc")]
    for j, (y, Q, pc) in enumerate(zip(ys, Qs, ctx.pcs)):
        L += box_minmax(y, Q)[0]
        terms.append((conj_ball(y), pc, ("pc", j)))
    for vt, tb in zip(vts, tubes):
        vtc = conj_ball(vt)
        if tb[0] == "iv":
            ok, bnd = iv_bounds(tb, vt, +1, cache)
            if not ok:
                return "empty leaf: interval-tube sign condition fails"
            L += bnd
            terms.append((vtc, iv_subballs(tb), ("ivlist",) + tb))
            continue
        c, a, g, r = tube_data(tb, tau_N, cache)
        if not ((vtc * g).real >= 0):
            return "empty leaf: tube sign condition fails"
        L += (vtc * a).real - absq(vt) * r
        terms.append((vtc, c, ("c",) + tb))
    L = arb(L.lower())
    if not (L > 0):
        return "empty leaf: L > 0 fails"
    if not t_sweep_below(terms, tau_N, L, getattr(ctx, "kc", None)):
        return "empty leaf: t-sweep fails"
    return None

def check_w1_arc(ctx, tile, q0, q1, Qs, tubes, u, v, ys, vts, tau_N, r1, cache, depth=0):
    uc = conj_ball(u); vc = conj_ball(v)
    X = (vc * ctx.Sc).real
    if not (X <= 0):
        return False
    P = ell_ball(tile, q0, q1)
    L = (uc * S(P)).real - X - absq(v) * r1
    terms = [(uc, P), (-vc, ctx.zc, "zc")]
    for j, (y, Q, pc) in enumerate(zip(ys, Qs, ctx.pcs)):
        L -= box_minmax(y, Q)[1]
        terms.append((-conj_ball(y), pc, ("pc", j)))
    for vt, tb in zip(vts, tubes):
        vtc = conj_ball(vt)
        if tb[0] == "iv":
            ok, bnd = iv_bounds(tb, vt, -1, cache)
            if not ok:
                return False
            L -= bnd
            terms.append((-vtc, iv_subballs(tb), ("ivlist",) + tb))
            continue
        c, a, g, r = tube_data(tb, tau_N, cache)
        if not ((vtc * g).real <= 0):
            return False
        L -= (vtc * a).real + absq(vt) * r
        terms.append((-vtc, c, ("c",) + tb))
    L = arb(L.lower())
    if L > 0 and t_sweep_below(terms, tau_N, L, getattr(ctx, "kc", None)):
        return True
    if depth >= 4:
        return False
    m = (q0 + q1) / 2
    return (check_w1_arc(ctx, tile, q0, m, Qs, tubes, u, v, ys, vts, tau_N, r1, cache, depth + 1) and
            check_w1_arc(ctx, tile, m, q1, Qs, tubes, u, v, ys, vts, tau_N, r1, cache, depth + 1))


def diag_w1_arc(ctx, tile, q0, q1, Qs, tubes, u, v, ys, vts, tau_N, r1, cache):
    """diagnostic only: which stage of the W1 check fails at the given arc (no subdivision); returns a string."""
    uc = conj_ball(u); vc = conj_ball(v)
    X = (vc * ctx.Sc).real
    if not (X <= 0): return "X>0"
    P = ell_ball(tile, q0, q1)
    L = (uc * S(P)).real - X - absq(v) * r1
    parts = [("base", float(L.lower()))]
    terms = [(uc, P), (-vc, ctx.zc, "zc")]
    for vt, tb in zip(vts, tubes):
        vtc = conj_ball(vt)
        ok, bnd = iv_bounds(tb, vt, -1, cache)
        if not ok: return "iv sign"
        L -= bnd; parts.append(("ivbnd", float(bnd.upper())))
        terms.append((-vtc, iv_subballs(tb), None))
    L = arb(L.lower())
    if not (L > 0): return f"L<=0 {float(L.lower()):.3e} parts {parts}"
    # sup of tau*phi over t by a fixed-depth sweep
    tau = A(tau_N); worst = None
    for kk in range(2 ** 10):
        T = tcell(10, kk); phi = arb(0)
        for term in terms:
            coef, z = term[0], term[1]
            if isinstance(z, list):
                tv = None
                for zi in z:
                    v_ = (coef * K(T, zi)).real; tv = v_ if tv is None else tv.union(v_)
                phi += tv
            else:
                phi += (coef * K(T, z)).real
        up = float((tau * phi).upper())
        if worst is None or up > worst[0]: worst = (up, kk)
    return f"t-sweep: L={float(L.lower()):.3e}, max tau*phi (depth 10) = {worst[0]:.3e} at cell {worst[1]}"

def winding(tile, ts, ms):
    total = arb(0)
    todo = [(Fraction(k, 1024), Fraction(k + 1, 1024)) for k in range(1024)]
    while todo:
        q0, q1 = todo.pop()
        B = G_atoms(ell_ball(tile, q0, q1), ts, ms)
        if B.abs_lower() > 0 and B.rad() < 0.5 * B.abs_lower():
            g0 = G_atoms(ell_ball(tile, q0, q0), ts, ms)
            g1 = G_atoms(ell_ball(tile, q1, q1), ts, ms)
            total += (g1 / g0).arg()
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

def check_W(ctx, Qs, tubes, lf, cache, stats, defer=None):
    tau_N = Fraction(lf.get("tau_rep", str(G["tau"])))
    if tau_N < G["tau"]:
        return "W leaf: tau_rep < tau"
    if lf["tile"] not in G["tiles"]:
        return "W leaf: unknown tile"
    tile = G["tiles"][lf["tile"]]
    r1 = r1_bound(ctx.s0, ctx.s1, ctx.sc, tau_N)
    ts = [Fraction(t) for t in lf["wrep_t"]]; ms = [Fraction(x) for x in lf["wrep_m"]]
    sigma = Fraction(lf["sigma"]); raw = lf.get("mus", [])
    if len(raw) != len(tubes):
        return "W leaf: mus count mismatch"
    mus = []
    for x, tb in zip(raw, tubes):
        if tb[0] == "iv":
            if not isinstance(x, list) or len(x) != 2:
                return "W leaf: interval tube needs [q_r, mu_r]"
            qr, mu = Fraction(x[0]), Fraction(x[1])
            if not (tb[2] <= qr <= tb[3]):
                return "W leaf: q_r outside its hard arc"
            mus.append((qr, mu))
        else:
            if isinstance(x, list):
                return "W leaf: disc tube needs a scalar mu"
            mus.append((None, Fraction(x)))
    if (any(x < 0 for x in ms) or sum(ms) > tau_N or any(not (Fraction(-1, 2) <= t <= Fraction(1, 2)) for t in ts)
            or sigma < 1 or any(mu < 0 for _, mu in mus)):
        return "W leaf: w_rep not admissible"
    if not ((what_atoms(ctx.zc, ts, ms) - A(sigma) * ctx.Sc).abs_upper() <= r1):
        return "W leaf: w_rep violates the crossing disc"
    for pc, (x0, x1, y0, y1) in zip(ctx.pcs, Qs):
        wp = what_atoms(pc, ts, ms)
        if not (wp.real >= A(x0) and wp.real <= A(x1) and wp.imag >= A(y0) and wp.imag <= A(y1)):
            return "W leaf: w_rep-hat(p_j) not in its box"
    for (qr, mu), tb in zip(mus, tubes):
        if tb[0] == "iv":
            zr = ell_ball(tb[1], qr, qr)
            if not ((what_atoms(zr, ts, ms) - S(zr) - A(mu) * G_atoms(zr, tb[4], tb[5])).abs_upper() <= A(G["iv_eps"])):
                return "W leaf: w_rep violates an interval tube"
            continue
        c, a, g, r = tube_data(tb, tau_N, cache)
        if not ((what_atoms(c, ts, ms) - a - A(mu) * g).abs_upper() <= r):
            return "W leaf: w_rep violates a tube"
    n = winding(tile, ts, ms)
    if n is None or n % 2 == 0:
        return f"W leaf: winding {n} not odd"
    # tile arcs: W1 or hard, tiling [0,1]
    m = len(ctx.pcs); K_ = len(tubes)
    items = []
    for idx, a in enumerate(lf["tile_arcs"]):
        if isinstance(a, dict):
            q0, q1 = Fraction(a["hard"][0]), Fraction(a["hard"][1])
            kind = a.get("kind")
            if kind != "iv":                  # vC (i): only interval tubes; "disc" or a missing kind fails
                return "W leaf: hard-arc kind must be 'iv'"
            items.append((q0, q1, "hard:" + kind, a["child"], idx))
        else:
            if len(a) != 6 + 2 * m + 2 * K_:
                return "W leaf: wrong tile arc length"
            items.append((Fraction(a[0]), Fraction(a[1]), "w1", a, idx))
    items.sort(key=lambda x: x[0])
    if not items or items[0][0] != 0 or items[-1][1] != 1:
        return "W leaf: tile arcs do not cover [0,1]"
    for i in range(len(items)):
        if not items[i][0] < items[i][1]:
            return "W leaf: empty tile arc"
        if i + 1 < len(items) and items[i][1] != items[i + 1][0]:
            return "W leaf: tile arcs not contiguous"
    for q0, q1, kind, a, idx in items:
        if kind == "w1":
            u = cplx(a[2:4]); v = cplx(a[4:6])
            ys = [cplx(a[6 + 2 * j: 8 + 2 * j]) for j in range(m)]
            vts = [cplx(a[6 + 2 * m + 2 * k: 8 + 2 * m + 2 * k]) for k in range(K_)]
            if not check_w1_arc(ctx, tile, q0, q1, Qs, tubes, u, v, ys, vts, tau_N, r1, cache):
                return f"W1 fails on tile arc [{q0},{q1}] (tile {lf['tile']}, depth {len(tubes)})"
        else:
            stats["hard"] = stats.get("hard", 0) + 1
            if defer is not None:          # --deep mode: the child subtree is checked as a separate job
                defer.append(idx)
                continue
            newtube = (kind.split(":")[1], tile, q0, q1, tuple(ts), tuple(ms))
            err = check_tree(ctx, a, list(Qs), tubes + [newtube], cache, stats)
            if err:
                return f"hard arc [{q0},{q1}] -> {err}"
    return None

def check_tree(ctx, node, Qs, tubes, cache, stats, defer=None):
    if "ivsplit" in node:
        # local refinement of interval tube k: kids use [q0, qm] and [qm, q1] (arc split)
        k = node["ivsplit"]
        if not (isinstance(k, int) and 0 <= k < len(tubes)) or tubes[k][0] != "iv":
            return "bad ivsplit node (tube index)"
        kind, tile, q0, q1, ts, ms = tubes[k]
        qm = Fraction(node["at"])
        if not (q0 < qm < q1) or len(node.get("kids", [])) != 2:
            return "bad ivsplit node (split point or kids)"
        stats["ivsplit"] = stats.get("ivsplit", 0) + 1
        for (a, b), kid in zip(((q0, qm), (qm, q1)), node["kids"]):
            t2 = list(tubes); t2[k] = ("iv", tile, a, b, ts, ms)
            err = check_tree(ctx, kid, list(Qs), t2, cache, stats)
            if err:
                return f"ivsplit tube {k} [{a},{b}] -> {err}"
        return None
    if "split" in node:
        k = node["split"]
        if not (0 <= k < len(Qs)) or len(node["kids"]) != 4:
            return "bad split node"
        x0, x1, y0, y1 = Qs[k]
        mx = (x0 + x1) / 2; my = (y0 + y1) / 2
        for kid, q in zip(node["kids"], [(x0, mx, y0, my), (mx, x1, y0, my), (x0, mx, my, y1), (mx, x1, my, y1)]):
            Q2 = list(Qs); Q2[k] = q
            err = check_tree(ctx, kid, Q2, tubes, cache, stats)
            if err:
                return err
        return None
    boxes = [tuple(Fraction(b) for b in bx) for bx in node.get("boxes", [])]
    if boxes != list(Qs):
        return "leaf boxes do not match their tree position"
    stats["leaves"] = stats.get("leaves", 0) + 1
    if node["type"] == "empty":
        stats["empty"] = stats.get("empty", 0) + 1
        return check_empty(ctx, Qs, tubes, node, cache)
    if node["type"] == "W":
        stats["W"] = stats.get("W", 0) + 1
        stats["maxdepth"] = max(stats.get("maxdepth", 0), len(tubes))
        return check_W(ctx, Qs, tubes, node, cache, stats, defer=defer)
    return "unknown leaf type"

# ---------------------------------------------------------------- arcs
def check_E(s0, s1, u, depth=0):
    tau = A(G["tau"])
    z = ell_ball(G["T1"], s0, s1)
    uc = conj_ball(u)
    Sz = S(z)
    ok = bool((uc * Sz).real > 0)
    if ok:
        stack = [(Fraction(-1, 2), Fraction(1, 2), 0)]
        while stack:
            t0, t1, dpt = stack.pop()
            if (uc * (Sz - tau * K(hull(t0, t1), z))).real > 0:
                continue
            if dpt >= TDEPTH:
                ok = False
                break
            m = (t0 + t1) / 2
            stack += [(t0, m, dpt + 1), (m, t1, dpt + 1)]
    if ok:
        return True
    if depth >= 4:
        return False
    m = (s0 + s1) / 2
    return check_E(s0, m, u, depth + 1) and check_E(m, s1, u, depth + 1)

def arc_context(arc):
    """(ctx, tree, Qs) for a rooted arc, or (error string, None, None)."""
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        return "sc outside arc", None, None
    ctx = Ctx(); ctx.s0, ctx.s1, ctx.sc = s0, s1, sc
    ctx.zc = ell_ball(G["T1"], sc, sc); ctx.Sc = S(ctx.zc); ctx.kc = {}
    if arc["type"] == "H":
        ctx.pcs = []
        tree = {"boxes": [], "type": "W", "tile": arc["tile"], "tile_arcs": arc["tile_arcs"], "wrep_t": arc["wrep_t"],
                "wrep_m": arc["wrep_m"], "sigma": arc["sigma"]}
        return ctx, tree, []
    pts = [cplx(p) for p in arc.get("pcs", [])]
    ctx.pcs = [acb(A(a), A(b)) for a, b in pts]
    Rs = [Fraction(R) for R in arc.get("Rs", [])]
    if len(Rs) != len(pts):
        return "Rs/pcs mismatch", None, None
    for (a, b), R in zip(pts, Rs):
        if not (A(R) >= A(G["tau"]) * (PI * abs(A(b))).exp()):
            return "R too small", None, None
    return ctx, arc["tree"], [(-R, R, -R, R) for R in Rs]

ARCS = []
def work_shallow(i):
    """--deep mode, pass 1: everything of arc i except the subtrees below the hard arcs of a ROOT W leaf (returned as jobs)."""
    arc = ARCS[i]
    if arc["type"] == "E":
        ok = check_E(Fraction(arc["s0"]), Fraction(arc["s1"]), cplx(arc["u"]))
        return i, (None if ok else "E fails"), {}, []
    ctx, tree, Qs = arc_context(arc)
    if tree is None:
        return i, ctx, {}, []
    stats = {}; defer = []
    root_w = "split" not in tree and "ivsplit" not in tree and tree.get("type") == "W"
    try:
        err = check_tree(ctx, tree, Qs, [], {}, stats, defer=defer if root_w else None)
    except (ValueError, KeyError, TypeError, IndexError) as e:
        err = f"malformed or failing data: {type(e).__name__}: {e}"
    return i, err, stats, [(i, idx) for idx in defer]

def work_child(job):
    """--deep mode, pass 2: the subtree below hard arc number idx (tile_arcs index) of arc i's root W leaf."""
    i, idx = job
    arc = ARCS[i]
    ctx, tree, Qs = arc_context(arc)
    stats = {}
    try:
        a = tree["tile_arcs"][idx]
        tile = G["tiles"][tree["tile"]]
        q0, q1 = Fraction(a["hard"][0]), Fraction(a["hard"][1])
        ts = tuple(Fraction(t) for t in tree["wrep_t"]); ms = tuple(Fraction(x) for x in tree["wrep_m"])
        if a.get("kind") != "iv":                 # vC (i): only interval tubes; "disc" or a missing kind fails
            err = f"hard arc [{q0},{q1}] -> hard-arc kind must be 'iv'"
        else:
            newtube = ("iv", tile, q0, q1, ts, ms)
            err = check_tree(ctx, a["child"], list(Qs), [newtube], {}, stats)
            if err:
                err = f"hard arc [{q0},{q1}] -> {err}"
    except (ValueError, KeyError, TypeError, IndexError) as e:
        err = f"malformed or failing data: {type(e).__name__}: {e}"
    return i, idx, err, stats

def check_rooted(arc):
    s0, s1, sc = Fraction(arc["s0"]), Fraction(arc["s1"]), Fraction(arc["sc"])
    if not (s0 <= sc <= s1):
        return "sc outside arc", {}
    ctx = Ctx(); ctx.s0, ctx.s1, ctx.sc = s0, s1, sc
    ctx.zc = ell_ball(G["T1"], sc, sc); ctx.Sc = S(ctx.zc); ctx.kc = {}
    if arc["type"] == "H":
        ctx.pcs = []
        tree = {"boxes": [], "type": "W", "tile": arc["tile"], "tile_arcs": arc["tile_arcs"], "wrep_t": arc["wrep_t"],
                "wrep_m": arc["wrep_m"], "sigma": arc["sigma"]}
        Qs = []
    else:
        pts = [cplx(p) for p in arc.get("pcs", [])]
        ctx.pcs = [acb(A(a), A(b)) for a, b in pts]
        Rs = [Fraction(R) for R in arc.get("Rs", [])]
        if len(Rs) != len(pts):
            return "Rs/pcs mismatch", {}
        for (a, b), R in zip(pts, Rs):
            if not (A(R) >= A(G["tau"]) * (PI * abs(A(b))).exp()):
                return "R too small", {}
        tree = arc["tree"]
        Qs = [(-R, R, -R, R) for R in Rs]
    stats = {}
    try:
        err = check_tree(ctx, tree, Qs, [], {}, stats)
    except (ValueError, KeyError, TypeError, IndexError) as e:
        err = f"malformed or failing data: {type(e).__name__}: {e}"
    return err, stats

def work(item):
    kind, arc = item
    if kind == "E":
        ok = check_E(Fraction(arc["s0"]), Fraction(arc["s1"]), cplx(arc["u"]))
        return (None if ok else "E fails"), {}
    return check_rooted(arc)

def init(g):
    G.update(g)

def main(path, nproc, subset=False, deep=False):
    if path.endswith(".gz"):
        import gzip
        with gzip.open(path, "rt") as fh:
            C = json.load(fh)
    else:
        with open(path) as fh:
            C = json.load(fh)
    assert C["variant"] == "Cp"
    tau = Fraction(C["tau"])
    assert 0 < tau < 1
    c, a, b = (Fraction(x) for x in C["T1"])
    assert a > 0 and b > 0
    lo, hi = c - a, c + a
    ints = [n for n in range(int(lo) - 2, int(hi) + 3) if n != 0 and lo < n < hi]
    assert len(ints) == 1, "T1 must enclose exactly one zero of S"
    assert not (lo.denominator == 1 and lo != 0) and not (hi.denominator == 1 and hi != 0), "S vanishes on T1"
    tiles = {}
    for key, tl in C["tiles"].items():
        cr, ci, ta, tb = (Fraction(x) for x in tl)
        assert ta > 0 and tb > 0
        tiles[key] = (cr, ci, ta, tb)
    arcs = sorted(C["arcs"], key=lambda x: Fraction(x["s0"]))
    if subset:
        print("SUBSET CHECK of individual arcs (NOT a certificate check: coverage of [0,1] is not tested)")
    else:
        assert Fraction(arcs[0]["s0"]) == 0 and Fraction(arcs[-1]["s1"]) == 1, "arcs must cover [0,1]"
    for i in range(len(arcs)):
        assert Fraction(arcs[i]["s0"]) < Fraction(arcs[i]["s1"])
        if i + 1 < len(arcs) and not subset:
            assert Fraction(arcs[i]["s1"]) == Fraction(arcs[i + 1]["s0"]), "arcs not contiguous"
    iv_eps = Fraction(C.get("iv_eps", "1/1000000000"))
    assert 0 <= iv_eps <= Fraction(1, 1000), "iv_eps out of range"
    g = {"tau": tau, "T1": (c, Fraction(0), a, b), "tiles": tiles, "iv_eps": iv_eps}
    items = [(arc["type"], arc) for arc in arcs]
    assert all(k in ("E", "H", "H3", "N") for k, _ in items)
    if deep:
        # same conditions as below, scheduled finer: pass 1 checks each arc except the subtrees under the hard arcs of a root
        # W leaf; pass 2 checks those subtrees as separate jobs; an arc passes iff its pass-1 check and all its jobs pass
        global ARCS
        ARCS = arcs
        G.update(g)
        res = [None] * len(arcs); jobs = []
        with Pool(nproc, initializer=init, initargs=(g,)) as pool:
            for i, err, st, jb in pool.imap_unordered(work_shallow, range(len(arcs)), chunksize=1):
                res[i] = [err, dict(st)]; jobs += jb
            print(f"deep mode: pass 1 done ({len(arcs)} arcs), {len(jobs)} subtree jobs", flush=True)
            for i, idx, err, st in pool.imap_unordered(work_child, jobs, chunksize=1):
                if err is not None and res[i][0] is None:
                    res[i][0] = err
                for k_, v_ in st.items():
                    res[i][1][k_] = max(res[i][1].get(k_, 0), v_) if k_ == "maxdepth" else res[i][1].get(k_, 0) + v_
        res = [tuple(r) for r in res]
    else:
        with Pool(nproc, initializer=init, initargs=(g,)) as pool:
            res = pool.map(work, items, chunksize=1)
    bad = [(arcs[i]["s0"], r[0]) for i, r in enumerate(res) if r[0] is not None]
    if subset:
        for i, r in enumerate(res):
            print(f"  arc s0={arcs[i]['s0']} type {arcs[i]['type']}: {'OK' if r[0] is None else 'FAIL: ' + r[0]} {r[1]}")
        print(f"SUBSET: {len(items) - len(bad)} of {len(items)} arcs pass")
        if bad:                               # vC (iii): a failing arc makes the run exit non-zero
            sys.exit(1)
        return
    tot = {}
    for _, st in res:
        for k, v in st.items():
            tot[k] = max(tot.get(k, 0), v) if k == "maxdepth" else tot.get(k, 0) + v
    nE = sum(1 for k, _ in items if k == "E")
    if bad:
        print(f"FAILED: {len(bad)} of {len(items)} arcs; first: {bad[0]}")
        sys.exit(1)
    bound = 1 / (1 - tau)
    print(f"OK: nested certificate, tau = {tau} = {float(tau)}; {nE} E arcs, {len(items) - nE} rooted arcs verified; totals {tot}")
    print(f"=> ess sup f*f > {bound} (int f)^2 = {float(bound):.10f} (int f)^2, so C >= C' >= {bound}")

if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if a not in ("--subset", "--deep")]
    main(args[0], int(args[1]) if len(args) > 1 else 8, subset="--subset" in sys.argv, deep="--deep" in sys.argv)
