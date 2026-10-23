# Search side for the THREE-LEVEL certificate (variant Cp); m6: optional level-4 points (cfg pc56) and tiles; m8: tile marked dead after any failed attempt in a node, LP budget per attempt; m9: strategy order l3_first, maxdepth3, SIGTERM terminates the pool.  Builds on gen_two_level.py.
# H arcs where the 2-level witness fails become H3 arcs: quadtree over boxes Q for the value w-hat(pc) (|w-hat(pc)| <= R),
# each leaf either 'empty' (no w in C_A with w-hat(pc) in Q) or 'W' (witness tile with duals (u, v, y)).
import numpy as np, json, sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_two_level import *          # Ell, Sball, Kball, A_, hull, rat, rA_bound, solve_E, solve_H(2-level), winding_count, TS, NT, Sf
from scipy.optimize import linprog
import hslp

# multi-point boxes: Qs = list of boxes ((x0,x1),(y0,y1)), one per point pc_j; ys = list of complex multipliers
def lp_empty_m(zc, pcs_, r, Qs, tau):
    """max m s.t. Re(conj v Sc) - r|v|_1 + sum_j min_{Qj} Re(conj(y_j)x) - tau*eta >= m,
       Re(conj v Kc) + sum_j Re(conj y_j Kq_j) <= eta, Re(conj v Sc) >= 0, |v|_1 + sum|y_j|_1 <= 1."""
    m = len(pcs_)
    Kc = np.exp(-2j*np.pi*TS*zc); Sc = Sf(zc); Kq = [np.exp(-2j*np.pi*TS*p) for p in pcs_]
    # x = [vr, vi, (yrp, yrm, yip, yim)*m, eta, ar, ai, mm]
    nv = 2 + 4*m + 4; ie = 2 + 4*m
    rows = []; rhs = []
    for i in range(NT):
        e = np.zeros(nv); e[0] = Kc[i].real; e[1] = Kc[i].imag
        for j in range(m):
            b = 2 + 4*j; e[b:b+4] = [Kq[j][i].real, -Kq[j][i].real, Kq[j][i].imag, -Kq[j][i].imag]
        e[ie] = -1; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[0] = -Sc.real; e[1] = -Sc.imag; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[0] = -Sc.real; e[1] = -Sc.imag
    for j, ((x0, x1), (y0, y1)) in enumerate(Qs):
        b = 2 + 4*j; e[b:b+4] = [-x0, x1, -y0, y1]
    e[ie] = tau; e[ie+1] = r; e[ie+2] = r; e[ie+3] = 1; rows.append(e); rhs.append(0)
    for (j, k) in [(0, ie+1), (1, ie+2)]:
        e = np.zeros(nv); e[j] = 1; e[k] = -1; rows.append(e); rhs.append(0)
        e = np.zeros(nv); e[j] = -1; e[k] = -1; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[2:2+4*m] = 1; e[ie+1] = 1; e[ie+2] = 1; rows.append(e); rhs.append(1)
    c = np.zeros(nv); c[ie+3] = -1
    bounds = [(None, None)]*2 + [(0, None)]*(4*m + 3) + [(None, None)]
    ok, x, _ = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), [b_[0] for b_ in bounds], [b_[1] for b_ in bounds], key=('empty', m))
    if not ok: return None
    return (x[0], x[1]), [(x[2+4*j] - x[3+4*j], x[4+4*j] - x[5+4*j]) for j in range(m)], x[ie+3]

def box_lo_hi(y, Q):
    (x0, x1), (y0, y1) = Q
    lo = (A_(y[0])*A_(x0) if y[0] >= 0 else A_(y[0])*A_(x1)) + (A_(y[1])*A_(y0) if y[1] >= 0 else A_(y[1])*A_(y1))
    hi = (A_(y[0])*A_(x1) if y[0] >= 0 else A_(y[0])*A_(x0)) + (A_(y[1])*A_(y1) if y[1] >= 0 else A_(y[1])*A_(y0))
    return lo, hi

def empty_ok_m(zcb, pcbs, Sc, rr, Qs, v, ys, tau, kc=None):
    vc = acb(A_(v[0]), -A_(v[1])); TAU = A_(tau)
    X = (vc*Sc).real
    if not (X >= 0): return False
    vabs = (A_(v[0])**2 + A_(v[1])**2).sqrt()
    lo = arb(0)
    for y, Q in zip(ys, Qs): lo += box_lo_hi(y, Q)[0]
    L = arb((X - vabs*rr + lo).lower())
    if not (L > 0): return False
    if kc is None: kc = KCache(zcb, pcbs)
    ycs = [acb(A_(y[0]), -A_(y[1])) for y in ys]
    stack = [(TD0, k) for k in range(2**TD0)]
    while stack:
        d, k = stack.pop()
        T, Kz, Kp = kc.get(d, k)
        phi = (vc*Kz).real
        for yc, K in zip(ycs, Kp): phi += (yc*K).real
        if TAU*phi < L: continue
        if d >= 18: return False
        stack += [(d+1, 2*k), (d+1, 2*k+1)]
    return True

def lp_wit_m(p, zc, pcs_, r, Qs, tau):
    m = len(pcs_)
    Kp = np.exp(-2j*np.pi*TS*p); Kc = np.exp(-2j*np.pi*TS*zc); Kq = [np.exp(-2j*np.pi*TS*q) for q in pcs_]; Sp = Sf(p); Sc = Sf(zc)
    # x = [ur, ui, vr, vi, (yrp, yrm, yip, yim)*m, eta, ar, ai, br, bi, mm]
    nv = 4 + 4*m + 6; ie = 4 + 4*m
    rows = []; rhs = []
    for i in range(NT):
        e = np.zeros(nv); e[:4] = [Kp[i].real, Kp[i].imag, -Kc[i].real, -Kc[i].imag]
        for j in range(m):
            b = 4 + 4*j; e[b:b+4] = [-Kq[j][i].real, Kq[j][i].real, -Kq[j][i].imag, Kq[j][i].imag]
        e[ie] = -1; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[2] = Sc.real; e[3] = Sc.imag; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[:4] = [-Sp.real, -Sp.imag, Sc.real, Sc.imag]
    for j, ((x0, x1), (y0, y1)) in enumerate(Qs):
        b = 4 + 4*j; e[b:b+4] = [x1, -x0, y1, -y0]
    e[ie] = tau; e[ie+1] = r; e[ie+2] = r; e[ie+5] = 1; rows.append(e); rhs.append(0)
    for (j, k) in [(2, ie+1), (3, ie+2), (0, ie+3), (1, ie+4)]:
        e = np.zeros(nv); e[j] = 1; e[k] = -1; rows.append(e); rhs.append(0)
        e = np.zeros(nv); e[j] = -1; e[k] = -1; rows.append(e); rhs.append(0)
    e = np.zeros(nv); e[4:4+4*m] = 1; e[ie+1:ie+5] = 1; rows.append(e); rhs.append(1)
    c = np.zeros(nv); c[ie+5] = -1
    bounds = [(None, None)]*4 + [(0, None)]*(4*m + 5) + [(None, None)]
    ok, x, _ = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), [b_[0] for b_ in bounds], [b_[1] for b_ in bounds], key=('wit', m))
    if not ok: return None
    return (x[0], x[1]), (x[2], x[3]), [(x[4+4*j] - x[5+4*j], x[6+4*j] - x[7+4*j]) for j in range(m)], x[ie+5]

# ---- speedups (generator only): dyadic t-cells (d, k) <-> [t0, t1] = [-1/2 + k/2^d, -1/2 + (k+1)/2^d] as exact arb balls,
# a per-arc cache of K_t at the fixed points zc, pc_j, a float winding prefilter, and a rigorous winding with shared endpoints.
TD0 = 4
def tcell(d, k): return arb(-0.5 + (k + 0.5)/2.0**d, 0.5/2.0**d)
class KCache:
    def __init__(self, zcb, pcbs): self.zcb, self.pcbs, self.c = zcb, pcbs, {}
    def get(self, d, k):
        e = self.c.get((d, k))
        if e is None:
            T = tcell(d, k); e = (T, Kball(T, self.zcb), [Kball(T, p) for p in self.pcbs]); self.c[(d, k)] = e
        return e

def winding_float(tile, ts, ms, n=4000):
    q = np.arange(n + 1)/n; z = tile.zf(q)
    t = np.array([float(x) for x in ts]); m = np.array([float(x) for x in ms])
    G = Sf(z) - (m[None, :]*np.exp(-2j*np.pi*z[:, None]*t[None, :])).sum(1)
    if np.min(np.abs(G)) < 1e-9: return None
    d = np.angle(G[1:]/G[:-1])
    if np.max(np.abs(d)) > 0.5: return None
    return int(round(d.sum()/(2*np.pi)))

def winding_rig(tile, ts, ms, npieces=4000):
    """as gen_two_level.winding_count (same pieces and tests), endpoint values shared between neighbouring pieces."""
    tsA = [A_(t) for t in ts]; msA = [A_(m) for m in ms]
    def G(z):
        g = Sball(z)
        for t, m in zip(tsA, msA): g -= m*Kball(t, z)
        return g
    total = arb(0); gprev = G(tile.zball(Fr(0), Fr(0)))
    for k in range(npieces):
        q0, q1 = Fr(k, npieces), Fr(k+1, npieces)
        B = G(tile.zball(q0, q1))
        if not (B.abs_lower() > 0) or not (B.rad() < 0.5*B.abs_lower()): return None
        g1 = G(tile.zball(q1, q1))
        total += (g1/gprev).arg(); gprev = g1
    w = total/(2*PI)
    n = int(round(float(w.mid())))
    if not (abs(w - n) < 0.25): return None
    return n

def wit_arc_ok_m(tile, q0, q1, zcb, pcbs, Sc, rr, Qs, u, v, ys, tau, kc=None):
    P = tile.zball(q0, q1)
    uc = acb(A_(u[0]), -A_(u[1])); vc = acb(A_(v[0]), -A_(v[1])); TAU = A_(tau)
    X = (vc*Sc).real
    if not (X <= 0): return False
    vabs = (A_(v[0])**2 + A_(v[1])**2).sqrt()
    hi = arb(0)
    for y, Q in zip(ys, Qs): hi += box_lo_hi(y, Q)[1]
    L = arb(((uc*Sball(P)).real - X - vabs*rr - hi).lower())
    if not (L > 0): return False
    if kc is None: kc = KCache(zcb, pcbs)
    ycs = [acb(A_(y[0]), -A_(y[1])) for y in ys]
    stack = [(TD0, k) for k in range(2**TD0)]
    while stack:
        d, k = stack.pop()
        T, Kz, Kp = kc.get(d, k)
        phi = (uc*Kball(T, P)).real - (vc*Kz).real
        for yc, K in zip(ycs, Kp): phi -= (yc*K).real
        if TAU*phi < L: continue
        if d >= 18: return False
        stack += [(d+1, 2*k), (d+1, 2*k+1)]
    return True

def wrep_lp_m(zc, pcs_, r, Qs, tau):
    K = np.exp(-2j*np.pi*TS*zc); Sc = Sf(zc); Kq = [np.exp(-2j*np.pi*TS*p) for p in pcs_]
    for (f, g) in [(0.9, 1e-2), (0.99, 1e-4), (0.999, 1e-7), (0.9999, 1e-9)]:
        rows = []; rhs = []
        rho = f*r*np.cos(np.pi/16)
        for k in range(16):
            e = np.exp(-1j*2*np.pi*k/16); rows.append(np.concatenate([(e*K).real, [-(e*Sc).real]])); rhs.append(rho)
        for Kj, ((x0, x1), (y0, y1)) in zip(Kq, Qs):
            dx = g*(x1 - x0); dy = g*(y1 - y0)
            rows += [np.concatenate([Kj.real, [0]]), -np.concatenate([Kj.real, [0]]), np.concatenate([Kj.imag, [0]]), -np.concatenate([Kj.imag, [0]])]
            rhs += [x1 - dx, -(x0 + dx), y1 - dy, -(y0 + dy)]
        ok, xx, fun = hslp.solve_ub(np.concatenate([np.ones(NT), [0]]), np.array(rows), np.array(rhs), [0.0]*NT + [1.0], [None]*(NT + 1), key=('wrep', len(Qs)))
        if not ok: continue
        class _R: pass
        res = _R(); res.x = xx; res.fun = fun
        w = res.x[:NT]; sig = res.x[NT]
        idx = np.nonzero(w > 1e-14)[0]
        ts_ = [Fr(-1, 2) + Fr(int(i), NT-1) for i in idx]; ms_ = [rat(w[i], 2**60) for i in idx]
        if sum(ms_) <= tau: return ts_, ms_, rat(sig, 2**60), res.fun
    return None

def fix_X(v, Sc, sign):
    """Rounding guard: the LP often makes X = Re(conj(v) Sc) binding at 0; after rationalizing v it may land on the wrong
    side by ~1e-13.  Shift v by sign*c*s' (s' ~ Sc, c tiny) so that sign*X >= 0 holds rigorously (sign = -1 for witness
    arcs, +1 for empty leaves).  The shift changes the other terms by O(c) ~ 1e-12."""
    vc = acb(A_(v[0]), -A_(v[1])); X = (vc*Sc).real
    if (X <= 0) if sign < 0 else (X >= 0): return v
    sr = rat(float(Sc.real.mid()), 2**60); si = rat(float(Sc.imag.mid()), 2**60)
    xu = abs(float(X.mid())) + float(X.rad())
    c = rat(4*xu/float(sr*sr + si*si) + 1e-16, 2**64)
    return (v[0] + sign*c*sr, v[1] + sign*c*si)

PROG_EVERY = int(os.environ.get("PROG_EVERY", "0"))   # progress line every N tree nodes (stderr)
PRIM5 = "T5"   # name prefix of the primary zero-5 tile for the split rule (set from cfg "prim5")
NEAR_ONLY = set(); NEAR_IM = 0.0   # set from cfg in main (inherited by forked workers)
MAX_SUB_LP = int(os.environ.get("MAX_SUB_LP", "1000000"))
MAXDEPTH3 = 99   # depth cap for the two-point strategy (cfg "maxdepth3")
PRE_START = {}     # (tile id, ntile0) -> index of the initial arc where the prescreen last failed (search order only)
def try_witness_m(tile, zc, pcs_, zcb, pcbs, Sc, rr, Qs, tau, ntile0, kc=None, info=None):
    arcs = []
    Qf = [((float(Q[0][0]), float(Q[0][1])), (float(Q[1][0]), float(Q[1][1]))) for Q in Qs]
    # prescreen: the LPs of the initial arcs first, starting where it failed last time (a tile with a margin < -0.05 on an
    # initial arc fails anyway; same result, sooner)
    pre = {}; key = (id(tile), ntile0); k0 = PRE_START.get(key, 0)
    for i in range(ntile0):
        k = (k0 + i) % ntile0
        q0, q1 = Fr(k, ntile0), Fr(k+1, ntile0)
        d = lp_wit_m(tile.zf(float((q0+q1)/2)), zc, pcs_, float(rr.upper()), Qf, float(tau))
        if d is None or d[3] < -0.05:
            PRE_START[key] = k
            if info is not None: info["prescreen_fail"] = True
            return None
        pre[(q0, q1)] = d
    todo = [(Fr(k, ntile0), Fr(k+1, ntile0)) for k in range(ntile0)]
    nlp = 0
    while todo:
        q0, q1 = todo.pop()
        if q1 - q0 < Fr(1, 2**12): return None
        d = pre.pop((q0, q1), None)
        if d is None:
            nlp += 1
            if nlp > MAX_SUB_LP: return None
            d = lp_wit_m(tile.zf(float((q0+q1)/2)), zc, pcs_, float(rr.upper()), Qf, float(tau))
        if d is not None and d[3] > 1e-7:
            u = (rat(d[0][0]), rat(d[0][1])); v = (rat(d[1][0]), rat(d[1][1])); ys = [(rat(a), rat(b)) for a, b in d[2]]
            v = fix_X(v, Sc, -1)
            if wit_arc_ok_m(tile, q0, q1, zcb, pcbs, Sc, rr, Qs, u, v, ys, tau, kc):
                arcs.append([str(q0), str(q1), str(u[0]), str(u[1]), str(v[0]), str(v[1])] + [str(c) for y in ys for c in y]); continue
        if d is None or d[3] < -0.05: return None
        m = (q0+q1)/2; todo += [(q0, m), (m, q1)]
    return arcs

DSWITCH = 8
SPLIT_RULE = os.environ.get("SPLIT_RULE", "fail_loc")
STRAT_ORDER = os.environ.get("STRAT_ORDER", "both_first")   # or "singles_first" (m4 order)   # "dswitch" (pc1 first for DSWITCH levels), "width", "fail_loc"
def tile_fail(tile, zc, pcs_, rr, Qf, tau, nq=32):
    best = None
    for i in range(nq):
        p = tile.zf((i + 0.5)/nq)
        d = lp_wit_m(p, zc, pcs_, float(rr.upper()), Qf, float(tau))
        mg = -1.0 if d is None else d[3]
        if best is None or mg < best[0]: best = (mg, p)
    return best
def choose_split(tiles, zc, pcs_, rr, Qs, Qf, tau, Rs, nq=32):
    """fail_loc: among the primary tiles (zero-3 tile, and zero-5 tile when there are > 2 points), take the one whose
    worst boundary LP margin is largest (closest to working) and split the box of the point nearest to its worst point;
    fallback (that margin >= 0): the box with the largest width relative to R_j."""
    k_w = max(range(len(pcs_)), key=lambda j: (Qs[j][0][1] - Qs[j][0][0])/Rs[j])
    if SPLIT_RULE == "width": return k_w
    fails = [tile_fail(t, zc, pcs_, rr, Qf, tau, nq) for t in tiles]
    mg, p = max(fails, key=lambda f: f[0])
    if mg >= 0: return k_w
    return min(range(len(pcs_)), key=lambda j: abs(p - pcs_[j]))

def solve_H3_ab(arg):
    ab, a = arg
    return ab, solve_H3(a)

def solve_H3(args):
    ell, s0, s1, tau, tiles3, pcs, ntile0, maxdepth = args
    r2 = solve_H((ell, s0, s1, tau, {"up": tiles3["T3up"], "down": tiles3["T3dn"]}, ntile0))
    if "fail" not in r2:
        if r2.get("type") == "H": r2["tile"] = "T3up" if r2["tile"] == "up" else "T3dn"
        return r2
    sc = (s0 + s1)/2
    zc = ell.zf(float(sc)); zcb = ell.zball(sc, sc); Sc = Sball(zcb)
    rr = rA_bound(ell, s0, s1, sc, tau)
    up = zc.imag >= 0
    names = [nm for nm in tiles3 if nm.endswith("up")] if up else [nm for nm in tiles3 if nm.endswith("dn")]
    if NEAR_ONLY and abs(zc.imag) >= NEAR_IM: names = [nm for nm in names if nm[:-2] not in NEAR_ONLY]
    reps = [(tr, rA_bound(ell, s0, s1, sc, tr)) for tr in (tau, tau*Fr(2001, 2000), tau*Fr(201, 200))]
    pcAll = pcs["up"] if up else pcs["dn"]
    strategies = [[pcAll[0]], [pcAll[1]], [pcAll[0], pcAll[1]]] if len(pcAll) == 2 else [pcAll]
    if len(pcAll) == 2 and STRAT_ORDER == "both_first": strategies = [strategies[2], strategies[0], strategies[1]]
    p56 = pcs.get("up56" if up else "dn56", [])
    if p56:
        l4 = [list(pcAll) + list(p56)]
        if STRAT_ORDER == "l3_first" and len(pcAll) == 2: strategies = [[pcAll[0], pcAll[1]]] + l4 + [[pcAll[0]], [pcAll[1]]]
        elif STRAT_ORDER in ("both_first", "level4_first"): strategies = l4 + strategies
        else: strategies = strategies + l4
    tree = None; last_err = None
    for pcF in strategies:
        pcs_ = [complex(float(a), float(b)) for a, b in pcF]; pcbs = [acb(A_(a), A_(b)) for a, b in pcF]
        Rs = [Fr(tau)*Fr(int(np.ceil(np.exp(np.pi*abs(p.imag))*1000)), 1000) for p in pcs_]
        m = len(pcs_)
        md = min(maxdepth, 11) if m == 1 else (min(maxdepth, MAXDEPTH3) if m == 2 else maxdepth)
        kc = KCache(zcb, pcbs)
        def bstr(Qs): return [[str(Q[0][0]), str(Q[0][1]), str(Q[1][0]), str(Q[1][1])] for Q in Qs]
        stats = {"nodes": 0, "leaves": 0, "t0": time.time()}
        def rec(Qs, depth):
            stats["nodes"] += 1
            if PROG_EVERY and stats["nodes"] % PROG_EVERY == 0:
                print(f"  [s0={s0} m={m}] nodes {stats['nodes']} leaves {stats['leaves']} depth {depth} widths "
                      f"{[round(float(Q[0][1]-Q[0][0]), 5) for Q in Qs]} {time.time()-stats['t0']:.0f}s", file=sys.stderr, flush=True)
            Qf = [((float(Q[0][0]), float(Q[0][1])), (float(Q[1][0]), float(Q[1][1]))) for Q in Qs]
            de = lp_empty_m(zc, pcs_, float(rr.upper()), Qf, float(tau))
            if de is not None and de[2] > 1e-7:
                v = (rat(de[0][0]), rat(de[0][1])); ys = [(rat(a), rat(b)) for a, b in de[1]]
                v = fix_X(v, Sc, +1)
                if empty_ok_m(zcb, pcbs, Sc, rr, Qs, v, ys, tau, kc):
                    stats["leaves"] += 1
                    return {"boxes": bstr(Qs), "type": "empty", "v": [str(v[0]), str(v[1])], "y": [[str(a), str(b)] for a, b in ys]}
            dead = set()
            for (tr, rrr) in reps:
                wr = wrep_lp_m(zc, pcs_, float(rrr.lower()), Qf, tr)
                if wr is None: continue
                ts_, ms_, sig, mass = wr
                for nm in names:
                    if nm in dead: continue
                    n = winding_float(tiles3[nm], ts_, ms_)
                    if n is None or n % 2 == 0: continue
                    info = {}
                    arcs = try_witness_m(tiles3[nm], zc, pcs_, zcb, pcbs, Sc, rrr, Qs, tr, ntile0, kc, info)
                    if arcs is None:
                        dead.add(nm)
                        continue
                    n = winding_rig(tiles3[nm], ts_, ms_)
                    if n is None or n % 2 == 0: continue
                    arcs.sort(key=lambda a: Fr(a[0]))
                    stats["leaves"] += 1
                    return {"boxes": bstr(Qs), "type": "W", "tile": nm, "tau_rep": str(tr), "tile_arcs": arcs,
                            "wrep_t": [str(t) for t in ts_], "wrep_m": [str(x) for x in ms_], "sigma": str(sig), "count": n}
            if depth >= md: raise RuntimeError(f"depth at boxes {Qf}")
            if m == 1: k = 0
            elif SPLIT_RULE == "dswitch":
                k = 0 if depth < DSWITCH else max(range(m), key=lambda j: (Qs[j][0][1] - Qs[j][0][0])/Rs[j])
            else:
                prim = [tiles3[next(nm for nm in names if nm.startswith("T3"))]]
                if m > 2: prim.append(tiles3[next(nm for nm in names if nm.startswith(PRIM5))])
                k = choose_split(prim, zc, pcs_, rr, Qs, Qf, tau, Rs)
            (x0, x1), (y0, y1) = Qs[k]; mx = (x0+x1)/2; my = (y0+y1)/2
            kids = []
            for q in [((x0, mx), (y0, my)), ((mx, x1), (y0, my)), ((x0, mx), (my, y1)), ((mx, x1), (my, y1))]:
                Q2 = list(Qs); Q2[k] = q; kids.append(rec(Q2, depth+1))
            return {"split": k, "kids": kids}
        try:
            tree = rec([((-R, R), (-R, R)) for R in Rs], 0)
            break
        except RuntimeError as e:
            last_err = str(e); tree = None
    if tree is None:
        return {"fail": last_err, "s0": str(s0)}
    return {"s0": str(s0), "s1": str(s1), "type": "H3", "sc": str(sc), "pcs": [[str(a), str(b)] for a, b in pcF],
            "Rs": [str(R) for R in Rs], "tree": tree}

if __name__ == "__main__":
    cfg = json.load(open(sys.argv[1]))
    tau = Fr(cfg["tau"])
    T1 = Ell((Fr(cfg["T1"][0]), Fr(0)), Fr(cfg["T1"][1]), Fr(cfg["T1"][2]))
    tiles3 = {}
    for nm, t in cfg["tiles"].items():       # upper-half tiles; lower = conjugates
        tiles3[nm + "up"] = Ell((Fr(t[0]), Fr(t[1])), Fr(t[2]), Fr(t[3]))
        tiles3[nm + "dn"] = Ell((Fr(t[0]), -Fr(t[1])), Fr(t[2]), Fr(t[3]))
    pcs = {"up": [(Fr(a), Fr(b)) for a, b in cfg["pc"]], "dn": [(Fr(a), -Fr(b)) for a, b in cfg["pc"]]}
    if cfg.get("pc56"):
        pcs["up56"] = [(Fr(a), Fr(b)) for a, b in cfg["pc56"]]; pcs["dn56"] = [(Fr(a), -Fr(b)) for a, b in cfg["pc56"]]
    PRIM5 = cfg.get("prim5", PRIM5)
    MAXDEPTH3 = int(cfg.get("maxdepth3", 99))
    nE = cfg.get("nE", 512); nH = cfg.get("nH", 4096); ntile0 = cfg.get("ntile0", 64)
    NEAR_ONLY.update(cfg.get("tiles_near", [])); NEAR_IM = float(cfg.get("near_im", 0.0))
    SPLIT_RULE = cfg.get("split_rule", SPLIT_RULE); STRAT_ORDER = cfg.get("strat_order", STRAT_ORDER)
    print("split rule", SPLIT_RULE, "strategy order", STRAT_ORDER, "near-only tiles", sorted(NEAR_ONLY), "near_im", NEAR_IM, flush=True)
    t0 = time.time()
    pool = Pool(cfg.get("procs", 48))
    import signal
    def _term(*a):
        pool.terminate(); sys.exit(1)
    signal.signal(signal.SIGTERM, _term)
    open(cfg["out"] + ".pid", "w").write(str(os.getpid()) + "\n")
    if "arcs_file" in cfg:
        arcs = []; fine = [(Fr(a), Fr(b)) for a, b in json.load(open(cfg["arcs_file"]))]
    else:
        coarse = [(Fr(k, nE), Fr(k+1, nE)) for k in range(nE)]
        resE = pool.map(solve_E, [(T1, a, b, tau) for a, b in coarse])
        arcs = []; hard = []
        for (a, b), r in zip(coarse, resE):
            if r is not None: arcs.append(r)
            else: hard.append((a, b))
        fine = []
        for (a, b) in hard:
            k = int((b - a)*nH); fine += [(a + Fr(i, nH), a + Fr(i+1, nH)) for i in range(k)]
    print(f"E arcs {len(arcs)}, fine hard arcs {len(fine)} ({time.time()-t0:.0f}s)", flush=True)
    # JSONL log: every arc result as it completes (unordered), then one refinement level of the failures
    jl = open(cfg["out"] + ".jsonl", "w")
    for r in arcs: jl.write(json.dumps({"level": -1, "result": r}) + "\n")
    jl.flush()
    md = cfg.get("maxdepth", 16)
    def run_level(arclist, level):
        out = []; done = 0
        for ab, r in pool.imap_unordered(solve_H3_ab, [((a, b), (T1, a, b, tau, tiles3, pcs, ntile0, md)) for a, b in arclist], chunksize=1):
            out.append((ab, r)); done += 1
            jl.write(json.dumps({"level": level, "s0": str(ab[0]), "s1": str(ab[1]), "result": r}) + "\n"); jl.flush()
            if done % max(1, len(arclist)//40) == 0:
                print(f"  level {level}: {done}/{len(arclist)}  fails {sum(1 for _, x in out if 'fail' in x)} ({time.time()-t0:.0f}s)", flush=True)
        return out
    pairs = run_level(fine, 0)
    failed = [ab for ab, r in pairs if "fail" in r]
    print(f"first pass: {len(failed)} failing arcs ({time.time()-t0:.0f}s)", flush=True)
    sub = []
    for (a, b) in failed: sub += [(a + (b - a)*Fr(i, 4), a + (b - a)*Fr(i+1, 4)) for i in range(4)]
    pairs1 = run_level(sub, 1)
    print(f"refine: {len(sub)} subarcs, {sum(1 for _, r in pairs1 if 'fail' in r)} failing ({time.time()-t0:.0f}s)", flush=True)
    jl.close()
    pool.close()
