# Search side for the TWO-LEVEL certificate (variant Cp: w >= 0, int w <= tau).
# T1 = ellipse around z=1. Each arc of T1 is either
#   E: no crossing possible: Re(conj(u)S(z)) > 0 and Re(conj(u)(S(z) - tau K_t(z))) > 0 for all t   (as in check_cert)
#   H: witness tile T (ellipse) such that for every w in C_A = {w : exists sigma>=1, |w-hat(zc) - sigma S(zc)| <= r_A}
#      G_w = S - w-hat has no zero on T (dual (u,v) per tile arc), and G_{w_rep} has an odd number of zeros inside T.
import numpy as np, json, sys, time, os
from fractions import Fraction as Fr
from scipy.optimize import linprog
from multiprocessing import Pool
import flint
from flint import arb, acb, fmpq
flint.ctx.prec = 64
NT = 801
TS = np.linspace(-0.5, 0.5, NT)

def Sf(z): return np.sin(np.pi*z)/(np.pi*z)
def A_(q): return arb(fmpq(q.numerator, q.denominator))
def hull(q0, q1): return A_(q0).union(A_(q1))
PI = arb.pi(); I = acb(0, 1)
def Sball(z): return (PI*z).sin()/(PI*z)
def Kball(T, z): return (-2*PI*I*T*z).exp()
def rat(x, den=2**40): return Fr(int(round(float(x)*den)), den)

class Ell:
    def __init__(self, c, a, b):   # c complex given as (cr, ci) Fractions; a, b Fractions
        self.cr, self.ci, self.a, self.b = c[0], c[1], a, b
    def zf(self, s): return float(self.cr) + float(self.a)*np.cos(2*np.pi*s) + 1j*(float(self.ci) + float(self.b)*np.sin(2*np.pi*s))
    def zball(self, s0, s1):
        S_ = hull(s0, s1)
        return acb(A_(self.cr) + A_(self.a)*(2*S_).cos_pi(), A_(self.ci) + A_(self.b)*(2*S_).sin_pi())

# ---------------- E arcs ----------------
def best_u_E(z, tau):
    K = np.exp(-2j*np.pi*TS*z); S = Sf(z)
    r = linprog([-S.real, -S.imag], A_ub=np.column_stack([K.real, K.imag]), b_ub=np.ones(NT), bounds=[(-1e6, 1e6)]*2, method='highs')
    return r.x[0], r.x[1], -r.fun
def E_ok(ell, s0, s1, ur, ui, tau):
    z = ell.zball(s0, s1); u = acb(A_(ur), -A_(ui)); TAU = A_(tau)
    Sz = Sball(z)
    if not ((u*Sz).real > 0): return False
    stack = [(Fr(-1, 2), Fr(1, 2), 0)]
    while stack:
        t0, t1, d = stack.pop()
        v = (u*(Sz - TAU*Kball(hull(t0, t1), z))).real
        if v > 0: continue
        if d >= 18: return False
        m = (t0+t1)/2; stack += [(t0, m, d+1), (m, t1, d+1)]
    return True

# ---------------- H arcs ----------------
def rA_bound(ell, s0, s1, sc, tau):
    """rigorous upper bound r for |w-hat(zc) - sigma S(zc)| given w-hat(z) = sigma S(z), z on the arc, mass <= tau."""
    Z = ell.zball(s0, s1); zc = ell.zball(sc, sc)
    d = (Z - zc).abs_upper()                       # >= |z - zc|
    ymax = max(Z.imag.abs_upper(), zc.imag.abs_upper())
    TAU = A_(tau)
    smax = TAU*(PI*ymax).exp()/Sball(Z).abs_lower()   # sigma <= tau e^{pi|Im z|}/|S(z)|
    # |S'| on the ball (contains the segment): S'(z) = (pi z cos(pi z) - sin(pi z))/(pi z^2)
    dS = (PI*Z*(PI*Z).cos() - (PI*Z).sin())/(PI*Z*Z)
    r = d*(TAU*PI*(PI*ymax).exp() + smax*dS.abs_upper())
    return arb(r.upper())

def dual_tile(p, zc, r, tau):
    """max m s.t. Re(conj(u)S(p)) - Re(conj(v)S(zc)) - r(|vr|+|vi|) - tau*eta >= m, phi(t) <= eta, eta >= 0,
    Re(conj(v)S(zc)) <= 0, |ur|+|ui|+|vr|+|vi| <= 1.   Returns (ur, ui, vr, vi, m)."""
    Kp = np.exp(-2j*np.pi*TS*p); Kc = np.exp(-2j*np.pi*TS*zc); Sp = Sf(p); Sc = Sf(zc)
    # x = [ur, ui, vr, vi, eta, ar, ai, br, bi, m]
    nv = 10
    rows = []; rhs = []
    for i in range(NT):
        rows.append([Kp[i].real, Kp[i].imag, -Kc[i].real, -Kc[i].imag, -1, 0, 0, 0, 0, 0]); rhs.append(0)
    rows.append([0, 0, Sc.real, Sc.imag, 0, 0, 0, 0, 0, 0]); rhs.append(0)
    rows.append([-Sp.real, -Sp.imag, Sc.real, Sc.imag, tau, r, r, 0, 0, 1]); rhs.append(0)
    for (j, k) in [(2, 5), (3, 6), (0, 7), (1, 8)]:
        e = [0]*nv; e[j] = 1; e[k] = -1; rows.append(e); rhs.append(0)
        e = [0]*nv; e[j] = -1; e[k] = -1; rows.append(e); rhs.append(0)
    rows.append([0, 0, 0, 0, 0, 1, 1, 1, 1, 0]); rhs.append(1)
    c = np.zeros(nv); c[9] = -1
    bounds = [(None, None)]*4 + [(0, None)]*5 + [(None, None)]
    res = linprog(c, A_ub=np.array(rows, float), b_ub=np.array(rhs, float), bounds=bounds, method='highs')
    if res.status != 0: return None
    x = res.x
    return (x[0], x[1], x[2], x[3], x[9])

def tile_arc_ok(tile, q0, q1, zcb, Sc, rr, u, v, tau):
    P = tile.zball(q0, q1)
    uc = acb(A_(u[0]), -A_(u[1])); vc = acb(A_(v[0]), -A_(v[1])); TAU = A_(tau)
    vabs = (A_(v[0])**2 + A_(v[1])**2).sqrt()
    X = (vc*Sc).real
    if not (X <= 0): return False
    L = (uc*Sball(P)).real - X - vabs*rr
    L = arb(L.lower())
    if not (L > 0): return False
    Kc_cache = {}
    stack = [(Fr(-1, 2), Fr(1, 2), 0)]
    while stack:
        t0, t1, d = stack.pop()
        T = hull(t0, t1)
        phi = (uc*Kball(T, P)).real - (vc*Kball(T, zcb)).real
        if TAU*phi < L: continue
        if d >= 18: return False
        m = (t0+t1)/2; stack += [(t0, m, d+1), (m, t1, d+1)]
    return True

def wrep_lp(zc, r=0.0):
    """min-mass w >= 0 (grid atoms) with |w-hat(zc) - sigma S(zc)| <= 0.9 r (inscribed 16-gon), sigma >= 1."""
    K = np.exp(-2j*np.pi*TS*zc); Sc = Sf(zc)
    nvar = NT + 1
    if r <= 0:
        A = np.vstack([np.concatenate([K.real, [-Sc.real]]), np.concatenate([K.imag, [-Sc.imag]])])
        res = linprog(np.concatenate([np.ones(NT), [0]]), A_eq=A, b_eq=[0, 0], bounds=[(0, None)]*NT + [(1, None)], method='highs')
    else:
        rho = 0.9*r*np.cos(np.pi/16)
        rows = []
        for k in range(16):
            e = np.exp(-1j*2*np.pi*k/16)
            rows.append(np.concatenate([(e*K).real, [-(e*Sc).real]]))
        res = linprog(np.concatenate([np.ones(NT), [0]]), A_ub=np.array(rows), b_ub=np.full(16, rho),
                      bounds=[(0, None)]*NT + [(1, None)], method='highs')
    w = res.x[:NT]; sig = res.x[NT]
    idx = np.nonzero(w > 1e-12)[0]
    ts = [Fr(-1, 2) + Fr(int(i), NT-1) for i in idx]
    ms = [rat(w[i], 2**50) for i in idx]
    return ts, ms, rat(sig, 2**50), res.fun

def winding_count(tile, ts, ms, npieces=4000):
    """rigorous winding number of G(z) = S(z) - sum m_k exp(-2 pi i t_k z) along the tile ellipse (counterclockwise)."""
    tsA = [A_(t) for t in ts]; msA = [A_(m) for m in ms]
    def G(z):
        g = Sball(z)
        for t, m in zip(tsA, msA): g -= m*Kball(t, z)
        return g
    total = arb(0)
    k = 0
    while k < npieces:
        q0, q1 = Fr(k, npieces), Fr(k+1, npieces)
        B = G(tile.zball(q0, q1))
        # ball must avoid 0 with margin
        if not (B.abs_lower() > 0) or not (B.rad() < 0.5*B.abs_lower()):
            return None
        g0 = G(tile.zball(q0, q0)); g1 = G(tile.zball(q1, q1))
        ratio = g1/g0
        total += ratio.arg()
        k += 1
    w = total/(2*PI)
    n = int(round(float(w.mid())))
    if not (abs(w - n) < 0.25): return None
    return n

def tile_for(zc, tiles):
    return tiles['up'] if zc.imag >= 0 else tiles['down']

def solve_H(args):
    ell, s0, s1, tau, tiles, ntile0 = args
    rE = solve_E((ell, s0, s1, tau))
    if rE is not None: return rE
    sc = (s0 + s1)/2
    zc = ell.zf(float(sc)); zcb = ell.zball(sc, sc); Sc = Sball(zcb)
    rr = rA_bound(ell, s0, s1, sc, tau)
    tile = tile_for(zc, tiles)
    arcs = []
    todo = [(Fr(k, ntile0), Fr(k+1, ntile0)) for k in range(ntile0)]
    while todo:
        q0, q1 = todo.pop()
        if q1 - q0 < Fr(1, 2**16): return {"fail": f"tile arc too small at q={float(q0)}", "s0": str(s0)}
        p = tile.zf(float((q0+q1)/2))
        d = dual_tile(p, zc, float(rr.upper()), float(tau))
        if d is not None and d[4] > 1e-7:
            ur, ui, vr, vi, val = d
            u = (rat(ur), rat(ui)); v = (rat(vr), rat(vi))
            if tile_arc_ok(tile, q0, q1, zcb, Sc, rr, u, v, tau):
                arcs.append([str(q0), str(q1), str(u[0]), str(u[1]), str(v[0]), str(v[1])]); continue
        m = (q0+q1)/2; todo += [(q0, m), (m, q1)]
    ts, ms, sig, mass = wrep_lp(zc)
    if sum(ms) > tau:
        ts, ms, sig, mass = wrep_lp(zc, float(rr.lower()))
    if sum(ms) > tau: return {"fail": f"w_rep mass {float(sum(ms))} > tau", "s0": str(s0)}
    n = winding_count(tile, ts, ms)
    if n is None or n % 2 == 0: return {"fail": f"count {n}", "s0": str(s0)}
    arcs.sort(key=lambda a: Fr(a[0]))
    return {"s0": str(s0), "s1": str(s1), "type": "H", "sc": str(sc), "tile": "up" if zc.imag >= 0 else "down",
            "tile_arcs": arcs, "wrep_t": [str(t) for t in ts], "wrep_m": [str(m) for m in ms], "sigma": str(sig), "count": n,
            "rA_used": float(rr.upper())}

def solve_E(args):
    ell, s0, s1, tau = args
    z = ell.zf(float((s0+s1)/2))
    ur, ui, ps = best_u_E(z, float(tau))
    nrm = max(abs(ur), abs(ui)); ur, ui = rat(ur/nrm), rat(ui/nrm)
    if ps > float(tau) and E_ok(ell, s0, s1, ur, ui, tau):
        return {"s0": str(s0), "s1": str(s1), "type": "E", "u": [str(ur), str(ui)]}
    return None

if __name__ == "__main__":
    cfg = json.load(open(sys.argv[1]))
    tau = Fr(cfg["tau"])
    T1 = Ell((Fr(cfg["T1"][0]), Fr(0)), Fr(cfg["T1"][1]), Fr(cfg["T1"][2]))
    tu = cfg["tile_up"]   # [cr, ci, a, b]
    tiles = {"up": Ell((Fr(tu[0]), Fr(tu[1])), Fr(tu[2]), Fr(tu[3])),
             "down": Ell((Fr(tu[0]), -Fr(tu[1])), Fr(tu[2]), Fr(tu[3]))}
    nE = cfg.get("nE", 512); nH = cfg.get("nH", 4096); ntile0 = cfg.get("ntile0", 64)
    t0 = time.time()
    pool = Pool(cfg.get("procs", 48))
    open(cfg["out"] + ".pid", "w").write(str(os.getpid()) + "\n")
    # pass 1: E attempts on coarse arcs
    coarse = [(Fr(k, nE), Fr(k+1, nE)) for k in range(nE)]
    resE = pool.map(solve_E, [(T1, a, b, tau) for a, b in coarse])
    arcs = []; hard = []
    for (a, b), r in zip(coarse, resE):
        if r is not None: arcs.append(r)
        else: hard.append((a, b))
    print(f"E arcs {len(arcs)}, hard coarse arcs {len(hard)}  ({time.time()-t0:.0f}s)", flush=True)
    # pass 2: split hard coarse arcs into H arcs of width 1/nH
    fine = []
    for (a, b) in hard:
        k = int((b - a)*nH)
        fine += [(a + Fr(i, nH), a + Fr(i+1, nH)) for i in range(k)]
    pairs = []
    done = 0
    for (ab, r) in zip(fine, pool.imap(solve_H, [(T1, a, b, tau, tiles, ntile0) for a, b in fine], chunksize=1)):
        pairs.append((ab, r)); done += 1
        if done % max(1, len(fine)//20) == 0: print(f"  H {done}/{len(fine)} ({time.time()-t0:.0f}s)", flush=True)
    # refinement of failed arcs (edges of the hard region): split into 8 and retry (E first, then H)
    for level in range(4):
        failed = [ab for ab, r in pairs if "fail" in r]
        if not failed: break
        pairs = [(ab, r) for ab, r in pairs if "fail" not in r]
        sub = []
        for (a, b) in failed:
            sub += [(a + (b - a)*Fr(i, 8), a + (b - a)*Fr(i+1, 8)) for i in range(8)]
        res = pool.map(solve_H, [(T1, a, b, tau, tiles, ntile0) for a, b in sub], chunksize=1)
        pairs += list(zip(sub, res))
        print(f"  refine level {level}: {len(failed)} failed -> {len(sub)} subarcs, "
              f"{sum(1 for r in res if 'fail' in r)} still failing ({time.time()-t0:.0f}s)", flush=True)
    resH = [r for ab, r in pairs]
    fails = [r for r in resH if "fail" in r]
    print(f"H arcs {len(resH)}, failures {len(fails)}", flush=True)
    for f in fails[:10]: print("   ", f)
    arcs += [r for r in resH if "fail" not in r]
    arcs.sort(key=lambda r: Fr(r["s0"]))
    cert = {"problem": "signed third autocorrelation: two-level (crossing + witness tile) certificate", "variant": "Cp",
            "tau": str(tau), "T1": [str(x) for x in (T1.cr, T1.a, T1.b)],
            "tiles": {"up": [str(x) for x in (tiles['up'].cr, tiles['up'].ci, tiles['up'].a, tiles['up'].b)],
                      "down": [str(x) for x in (tiles['down'].cr, tiles['down'].ci, tiles['down'].a, tiles['down'].b)]},
            "arcs": arcs, "complete": len(fails) == 0}
    json.dump(cert, open(cfg["out"], "w"))
    print("wrote", cfg["out"], "complete" if not fails else "INCOMPLETE", f"{time.time()-t0:.0f}s")
    pool.close()
