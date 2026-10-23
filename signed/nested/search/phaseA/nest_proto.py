# Float prototype (NOT rigorous): nested-crossing certificates with a base point for 6.4 (signed third autocorrelation, C').
# Node = convex set C of w >= 0, int w <= tau, cut out by "disc" constraints
#     D = (c, a, g, mu0, r):  exists mu >= mu0 with |w-hat(c) - a - mu g| <= r.
# Level-1 crossing on T1: (zc, 0, S(zc), 1, r_A).  A tile T with representative w0 (odd winding) either separates on every
# tile arc (W leaf), or its hard arcs A'' (W1 fails) each give a sub-node C n D'' with D'' = (c'', S(c''), G_{w0}(c''), 0, r'')
# (Lemma X: if all zeros of G_w are even there are z on T, mu >= 0 with w-hat(z) = S(z) + mu G_{w0}(z); arcs where W1 holds
# for C exclude the crossing because w_{s*} = (1-s*) w0 + s* w lies in C).
# usage: nest_proto.py TAU K [maxnest] [tiles cfg json]
import numpy as np, sys, os, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_two_level import Ell, Sf, TS, NT, rA_bound, Fr
import hslp

def Kv(z): return np.exp(-2j*np.pi*TS*z)
def dSf(z): return (np.pi*z*np.cos(np.pi*z) - np.sin(np.pi*z))/(np.pi*z*z)

def rep_lp(discs, tau_cap=None):
    """min-mass w on the t-grid inside all discs (inscribed 16-gons, graded shrink). Returns (w, mus, mass) or None."""
    n = len(discs)
    for f in (0.9, 0.99, 0.999):
        rows = []; rhs = []
        for i, D in enumerate(discs):
            Kc = Kv(D['c']); rho = f*D['r']*np.cos(np.pi/16)
            for k in range(16):
                e = np.exp(-1j*2*np.pi*k/16)
                row = np.zeros(NT + n); row[:NT] = (e*Kc).real; row[NT+i] = -(e*D['g']).real
                rows.append(row); rhs.append(rho + (e*D['a']).real)
        c = np.concatenate([np.ones(NT), np.zeros(n)])
        lo = [0.0]*NT + [D['mu0'] for D in discs]; hi = [None]*(NT + n)
        ok, x, fun = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), lo, hi, key=('rep', n))
        if ok: return x[:NT], x[NT:], fun
    return None

def w1_lp(p, discs, tau):
    """max margin m = Re(conj u S(p)) - sum_i [Re(conj v_i (a_i + mu0_i g_i)) + r_i |v_i|_1] - tau eta,
       eta >= max(0, phi(t)), phi = Re(conj u K_t(p)) - sum_i Re(conj v_i K_t(c_i)), Re(conj v_i g_i) <= 0, |u|_1 + sum|v_i|_1 <= 1."""
    n = len(discs)
    Kp = Kv(p); Sp = Sf(p)
    ie = 2 + 2*n; nv = ie + 1 + 2 + 2*n + 1; im = nv - 1
    A = np.zeros((NT + n + 1 + 2*(2 + 2*n) + 1, nv)); b = np.zeros(A.shape[0]); row = 0
    A[:NT, 0] = Kp.real; A[:NT, 1] = Kp.imag
    for i, D in enumerate(discs):
        Kc = Kv(D['c']); A[:NT, 2+2*i] = -Kc.real; A[:NT, 3+2*i] = -Kc.imag
    A[:NT, ie] = -1; row = NT
    for i, D in enumerate(discs):
        A[row, 2+2*i] = D['g'].real; A[row, 3+2*i] = D['g'].imag; row += 1
    A[row, 0] = -Sp.real; A[row, 1] = -Sp.imag
    for i, D in enumerate(discs):
        bb = D['a'] + D['mu0']*D['g']
        A[row, 2+2*i] = bb.real; A[row, 3+2*i] = bb.imag; A[row, ie+3+2*i] = D['r']; A[row, ie+4+2*i] = D['r']
    A[row, ie] = tau; A[row, im] = 1; row += 1
    for j in range(2 + 2*n):
        ja = ie + 1 + j
        A[row, j] = 1; A[row, ja] = -1; row += 1
        A[row, j] = -1; A[row, ja] = -1; row += 1
    A[row, ie+1:ie+3+2*n] = 1; b[row] = 1; row += 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(2 + 2*n) + [0.0]*(1 + 2 + 2*n) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=('w1', n))
    if not ok: return None
    return complex(x[0], x[1]), x[im]

def Gw(z, w):
    z = np.atleast_1d(z)
    return Sf(z) - (w[None, :]*np.exp(-2j*np.pi*z[:, None]*TS[None, :])).sum(1)

def winding(tile, w, n=4000):
    q = np.arange(n + 1)/n; z = tile.zf(q)
    nz = np.nonzero(w > 1e-14)[0]
    G = Sf(z) - (w[None, nz]*np.exp(-2j*np.pi*z[:, None]*TS[None, nz])).sum(1)
    if np.min(np.abs(G)) < 1e-9: return None
    d = np.angle(G[1:]/G[:-1])
    if np.max(np.abs(d)) > 0.5: return winding(tile, w, 4*n) if n < 64000 else None
    return int(round(d.sum()/(2*np.pi)))

def tile_scan(tile, discs, tau, N=512):
    """sample the W1 margin at N midpoints; hard = margin <= 1e-7 (some w in C vanishes there). Returns (hard_intervals, nlp,
    min positive margin)."""
    qs = (np.arange(N) + 0.5)/N; mg = np.empty(N)
    for i, q in enumerate(qs):
        r = w1_lp(tile.zf(q), discs, tau); mg[i] = -1.0 if r is None else r[1]
    hard = mg <= 1e-7
    iv = []; k = 0
    while k < N:
        if hard[k]:
            j = k
            while j + 1 < N and hard[j + 1]: j += 1
            iv.append((k/N, (j + 1)/N, float(mg[k:j+1].min()))); k = j + 1
        else: k += 1
    pos = mg[~hard]
    return iv, N, (float(pos.min()) if pos.size else None)

def merge_arcs(arcs):
    out = []
    for q0, q1, mg in arcs:
        if out and abs(out[-1][1] - q0) < 1e-12: out[-1] = (out[-1][0], q1, min(out[-1][2], mg))
        else: out.append((q0, q1, mg))
    if len(out) > 1 and out[0][0] == 0.0 and abs(out[-1][1] - 1.0) < 1e-12:   # wrap
        out[0] = (out[-1][0] - 1.0, out[0][1], min(out[0][2], out[-1][2])); out.pop()
    return out

def hard_disc(tile, q0, q1, w0, tau, ns=33):
    """D'' for a hard arc [q0,q1] of tile with base w0 (float bounds from samples, inflated)."""
    qs = np.linspace(q0, q1, ns); zs = tile.zf(qs); c = tile.zf((q0 + q1)/2)
    d = np.max(np.abs(zs - c))*1.02
    Y = np.max(np.abs(zs.imag)) + d
    G0s = Gw(zs, w0); g = Gw(c, w0)[0]
    Smax = np.max(np.abs(Sf(zs)))*1.05 + 1e-3; dSmax = np.max(np.abs(dSf(zs)))*1.1 + 1e-3
    mu_max = (tau*np.exp(np.pi*Y) + Smax)/(np.min(np.abs(G0s))*0.95)
    dw0 = np.sum(w0*2*np.pi*np.abs(TS)*np.exp(2*np.pi*np.abs(TS)*Y))
    r = d*(tau*np.pi*np.exp(np.pi*Y) + dSmax + mu_max*(dSmax + dw0))
    return {'c': c, 'a': Sf(c), 'g': g, 'mu0': 0.0, 'r': r}, mu_max

STATS = {}
NODE_BUDGET = int(os.environ.get("NODE_BUDGET", "400"))
LAST_TILE = {}
R_NEST = float(os.environ.get("R_NEST", "0.01"))   # nest deeper only from nodes whose own tube is this thin (else the parent bisects)
def solve_node(discs, tau, tiles, nest, maxnest, tag, log, minarc=1/2**16, r_self=0.0):
    """returns True if closed (float), with recursion on hard arcs up to maxnest nested crossings."""
    STATS['nodes'] = STATS.get('nodes', 0) + 1
    if STATS['nodes'] > NODE_BUDGET: raise RuntimeError("node budget")
    rr = rep_lp(discs)
    if rr is None or rr[2] > tau:
        STATS['empty'] = STATS.get('empty', 0) + 1
        log(f"{tag} EMPTY (min mass {None if rr is None else round(rr[2], 5)})"); return True
    w0 = rr[0]; mass = rr[2]
    # fast path: the tile that worked last at this nesting level, scanned directly at full resolution
    lt = LAST_TILE.get(nest)
    if lt is not None:
        n = winding(tiles[lt], w0)
        if n is not None and n % 2 == 1:
            iv, nlp, mpos = tile_scan(tiles[lt], discs, tau, N=512)
            STATS['lps'] = STATS.get('lps', 0) + nlp
            if not iv:
                STATS['W'] = STATS.get('W', 0) + 1
                log(f"{tag} W {lt} (rep mass {mass:.5f}, min margin {mpos:.2e}) [fast]"); return True
    cands = []
    for nm, tl in tiles.items():
        n = winding(tl, w0)
        if n is None or n % 2 == 0: continue
        iv, nlp, mpos = tile_scan(tl, discs, tau, N=64)
        STATS['lps'] = STATS.get('lps', 0) + nlp
        cands.append((sum(b - a for a, b, _ in iv), nm))
    if not cands:
        log(f"{tag} FAIL no odd tile (rep mass {mass:.5f})"); STATS['fail'] = STATS.get('fail', 0) + 1; return False
    cands.sort()
    best = None
    for _, nm in cands[:3]:
        iv, nlp, mpos = tile_scan(tiles[nm], discs, tau, N=512)
        STATS['lps'] = STATS.get('lps', 0) + nlp
        hl = sum(b - a for a, b, _ in iv)
        if not iv:
            STATS['W'] = STATS.get('W', 0) + 1; LAST_TILE[nest] = nm
            log(f"{tag} W {nm} (rep mass {mass:.5f}, min margin {mpos:.2e})"); return True
        if best is None or hl < best[2]: best = (nm, iv, hl)
    nm, hm, hl = best
    log(f"{tag} tile {nm} hard {len(hm)} intervals, total param {hl:.4f}: " +
        ", ".join(f"[{a:.4f},{b:.4f}]" for a, b, mg in hm[:6]) + f" (rep mass {mass:.5f})")
    if nest >= maxnest or (nest >= 1 and r_self > R_NEST):
        STATS['fail'] = STATS.get('fail', 0) + 1; return False
    tl = tiles[nm]; allok = True
    for (a, b, _) in hm:
        stack = [(a, b, 0)]
        while stack:
            q0, q1, dep = stack.pop()
            D, mu_max = hard_disc(tl, q0, q1, w0, tau)
            if D['r'] > 0.05:      # hopeless as a constraint: bisect without solving
                m = (q0 + q1)/2; stack += [(q0, m, dep + 1), (m, q1, dep + 1)]; continue
            sub = discs + [D]
            STATS['sub'] = STATS.get('sub', 0) + 1
            okk = solve_node(sub, tau, tiles, nest + 1, maxnest, tag + f"/{nm}[{q0:.5f},{q1:.5f}] r{D['r']:.2e} mu{mu_max:.1f}", log, r_self=D['r'])
            if okk: continue
            if q1 - q0 < minarc:
                allok = False; log(f"{tag} hard arc [{q0:.6f},{q1:.6f}] FAILS at min width"); break
            m = (q0 + q1)/2; stack += [(q0, m, dep + 1), (m, q1, dep + 1)]
        if not allok: break
    return allok

if __name__ == "__main__":
    tau = float(Fr(sys.argv[1])); k = int(sys.argv[2]); maxnest = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    cfgp = sys.argv[4] if len(sys.argv) > 4 else os.path.expanduser("cfg.json")
    cfg = json.load(open(cfgp))
    T1 = Ell((Fr(cfg["T1"][0]), Fr(0)), Fr(cfg["T1"][1]), Fr(cfg["T1"][2]))
    nH = 4096; s0, s1 = Fr(k, nH), Fr(k + 1, nH); sc = (s0 + s1)/2
    zc = T1.zf(float(sc)); up = zc.imag >= 0
    rA = float(rA_bound(T1, s0, s1, sc, Fr(sys.argv[1])).upper())
    tiles = {}
    for nm, t in cfg["tiles"].items():
        ci = float(Fr(t[1])) if up else -float(Fr(t[1]))
        tiles[nm] = Ell((Fr(t[0]), Fr(str(ci))), Fr(t[2]), Fr(t[3]))
    discs = [{'c': zc, 'a': 0j, 'g': Sf(zc), 'mu0': 1.0, 'r': rA}]
    t0 = time.time()
    def log(s): print(f"[{time.time()-t0:6.1f}s] {s}", flush=True)
    log(f"tau {tau:.6f} arc k={k} s={float(sc):.5f} zc={zc:.4f} rA={rA:.3e} maxnest {maxnest}")
    try:
        ok = solve_node(discs, tau, tiles, 0, maxnest, f"k{k}", log)
        log(f"RESULT {'CLOSED' if ok else 'OPEN'} stats {STATS}")
    except RuntimeError as e:
        log(f"RESULT BUDGET ({e}) stats {STATS}")
