# Interval tubes (float prototype, NOT rigorous).  A hard arc A'' of a tile with base w0 gives the constraint
#   exists z in A'', mu >= 0:  |w-hat(z) - S(z) - mu G0(z)| <= eps
# handled in the duals by sup/inf over the arc (no localisation radius, no mu_max term):
#   sign  Re(conj v G0(z)) <= 0 on A''   ->  Re(conj v g) + dG |v|_1 <= 0          (dG = d max|G0'|)
#   bound sup_A'' Re(conj v S(z))       ->  Re(conj v S(c)) + (dS + eps) |v|_1     (dS = d max|S'|)
#   phi   -Re(conj v K_t(z))            ->  -Re(conj v K_t(c)) + dK(t) |v|_1        (dK(t) = 2 pi |t| d e^{2 pi |t| Y})
# Node sets are convex hulls of the exact sets; the bounds are uniform in z, so separation/emptiness hold on the hulls.
import numpy as np, os
import nest_proto as NP, nest2 as N2
import hslp
NDIR_IN = int(os.environ.get('NDIR_IN', '64'))

EPS = 1e-7
def iv_disc(tile, q0, q1, w0, ns=33):
    qs = np.linspace(q0, q1, ns); zs = tile.zf(qs); c = tile.zf((q0 + q1)/2)
    d = np.max(np.abs(zs - c))*1.02
    Y = np.max(np.abs(zs.imag)) + d
    dG0 = NP.dSf(zs) + (w0[None, :]*2j*np.pi*NP.TS[None, :]*np.exp(-2j*np.pi*zs[:, None]*NP.TS[None, :])).sum(1)
    w0c = w0.copy()
    return {'kind': 'iv', 'c': c, 'a': NP.Sf(c), 'g': NP.Gw(c, w0)[0], 'mu0': 0.0, 'r': EPS,
            'dS': d*np.max(np.abs(NP.dSf(zs)))*1.1, 'dG': d*np.max(np.abs(dG0))*1.1, 'd': d, 'Y': Y,
            'zs': [tile.zf(q0 + (q1 - q0)*f) for f in (0.5, 0.0, 1.0, 0.25, 0.75)], 'G0f': lambda z: NP.Gw(z, w0c)[0],
            'tile': tile, 'q0': q0, 'q1': q1, 'w0': w0c}

def dK(D):
    return 2*np.pi*np.abs(NP.TS)*D['d']*np.exp(2*np.pi*np.abs(NP.TS)*D['Y'])

def rep_lp3(discs):
    n = len(discs); NT = NP.NT
    for f in (0.9, 0.99, 0.999, 0.9999):
        rows = []; rhs = []
        for i, D in enumerate(discs):
            Kc = NP.Kv(D['c'])
            if D.get('kind') == 'iv':
                e2 = 0.5*EPS
                for e in (1, -1, 1j, -1j):
                    row = np.zeros(NT + n); row[:NT] = (np.conj(e)*Kc).real; row[NT+i] = -(np.conj(e)*D['g']).real
                    rows.append(row); rhs.append(e2 + (np.conj(e)*D['a']).real)
                continue
            rho = f*D['r']*np.cos(np.pi/NDIR_IN)
            for k in range(NDIR_IN):
                e = np.exp(-1j*2*np.pi*k/NDIR_IN)
                row = np.zeros(NT + n); row[:NT] = (e*Kc).real; row[NT+i] = -(e*D['g']).real
                rows.append(row); rhs.append(rho + (e*D['a']).real)
        c = np.concatenate([np.ones(NT), np.zeros(n)])
        lo = [0.0]*NT + [D['mu0'] for D in discs]; hi = [None]*(NT + n)
        ok, x, fun = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), lo, hi, key=('rep3', n))
        if ok: return x[:NT], x[NT:], fun
    return None

def w1_lp3(p, discs, tau):
    n = len(discs); NT = NP.NT
    Kp = NP.Kv(p); Sp = NP.Sf(p)
    ie = 2 + 2*n; nv = ie + 1 + 2 + 2*n + 1; im = nv - 1
    A = np.zeros((NT + n + 1 + 2*(2 + 2*n) + 1, nv)); b = np.zeros(A.shape[0])
    A[:NT, 0] = Kp.real; A[:NT, 1] = Kp.imag
    for i, D in enumerate(discs):
        Kc = NP.Kv(D['c']); A[:NT, 2+2*i] = -Kc.real; A[:NT, 3+2*i] = -Kc.imag
        if D.get('kind') == 'iv':
            dk = dK(D); A[:NT, ie+3+2*i] = dk; A[:NT, ie+4+2*i] = dk
    A[:NT, ie] = -1; row = NT
    for i, D in enumerate(discs):
        A[row, 2+2*i] = D['g'].real; A[row, 3+2*i] = D['g'].imag
        if D.get('kind') == 'iv': A[row, ie+3+2*i] = D['dG']; A[row, ie+4+2*i] = D['dG']
        row += 1
    A[row, 0] = -Sp.real; A[row, 1] = -Sp.imag
    for i, D in enumerate(discs):
        bb = D['a'] + D['mu0']*D['g']; rr = D['r'] + (D['dS'] if D.get('kind') == 'iv' else 0.0)
        A[row, 2+2*i] = bb.real; A[row, 3+2*i] = bb.imag; A[row, ie+3+2*i] = rr; A[row, ie+4+2*i] = rr
    A[row, ie] = tau; A[row, im] = 1; row += 1
    for j in range(2 + 2*n):
        ja = ie + 1 + j
        A[row, j] = 1; A[row, ja] = -1; row += 1
        A[row, j] = -1; A[row, ja] = -1; row += 1
    A[row, ie+1:ie+3+2*n] = 1; b[row] = 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(2 + 2*n) + [0.0]*(1 + 2 + 2*n) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=('w13', n))
    if not ok: return None
    return complex(x[0], x[1]), x[im]


def _empty_l1(discs, tau): return empty_lp3_orig(discs, tau)
def empty_lp3(discs, tau):
    """max m: sum_disc [Re(conj v (a + mu0 g)) - r|v|_1] + sum_iv [Re(conj v S(c)) - (dS + eps)|v|_1] - tau eta >= m,
       eta >= sum_disc Re(conj v K_t(c)) + sum_iv [Re(conj v K_t(c)) + dK(t)|v|_1], eta >= 0,
       Re(conj v g) >= 0 (disc), Re(conj v g) - dG|v|_1 >= 0 (iv), sum |v|_1 <= 1.  Returns margin or None."""
    n = len(discs); NT = NP.NT
    nv = 2*n + 1 + 2*n + 1; ie = 2*n; im = nv - 1
    A = np.zeros((NT + n + 1 + 4*n + 1, nv)); b = np.zeros(A.shape[0])
    for i, D in enumerate(discs):
        Kc = NP.Kv(D['c']); A[:NT, 2*i] = Kc.real; A[:NT, 2*i+1] = Kc.imag
        if D.get('kind') == 'iv':
            dk = dK(D); A[:NT, ie+1+2*i] = dk; A[:NT, ie+2+2*i] = dk
    A[:NT, ie] = -1; row = NT
    for i, D in enumerate(discs):
        A[row, 2*i] = -D['g'].real; A[row, 2*i+1] = -D['g'].imag
        if D.get('kind') == 'iv': A[row, ie+1+2*i] = D['dG']; A[row, ie+2+2*i] = D['dG']
        row += 1
    for i, D in enumerate(discs):
        bb = D['a'] + D['mu0']*D['g']; rr = D['r'] + (D['dS'] if D.get('kind') == 'iv' else 0.0)
        A[row, 2*i] = -bb.real; A[row, 2*i+1] = -bb.imag; A[row, ie+1+2*i] = rr; A[row, ie+2+2*i] = rr
    A[row, ie] = tau; A[row, im] = 1; row += 1
    for j in range(2*n):
        ja = ie + 1 + j
        A[row, j] = 1; A[row, ja] = -1; row += 1
        A[row, j] = -1; A[row, ja] = -1; row += 1
    A[row, ie+1:ie+1+2*n] = 1; b[row] = 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(2*n) + [0.0]*(1 + 2*n) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=('empty3', n))
    if not ok: return None
    return x[im]

empty_lp3_orig = empty_lp3
def rep_search(discs, tau):
    """min-mass rep in E: the exact crossing of EVERY interval tube is tried at 5 points of its arc (product, centre first);
    stops at the first combination with mass <= tau. Returns (w, mus, mass) of the best found."""
    import itertools
    ivs = [i for i, D in enumerate(discs) if D.get('kind') == 'iv']
    if not ivs: return rep_lp3(discs)
    best = None
    for combo in itertools.islice(itertools.product(range(5), repeat=len(ivs)), 125):
        d2 = list(discs)
        for i, j in zip(ivs, combo):
            D = discs[i]; z = D['zs'][j]
            D2 = dict(D); D2['c'] = z; D2['a'] = NP.Sf(z); D2['g'] = D['G0f'](z); d2[i] = D2
        r = rep_lp3(d2)
        if r is not None and (best is None or r[2] < best[2]): best = r
        if best is not None and best[2] <= tau: return best
    return best

BASE_OPT = int(os.environ.get("BASE_OPT", "1"))
def base_opt(discs, tau_w, tile, hm, w_rep, npts=3):
    """LP: a base w0 in the node set (mass <= tau_w, level-1 polygon, iv tubes at their first witness points) maximizing
    min_j Re(conj(e_j) G_w0(c_j)) over points c_j of the hard intervals, e_j = direction of G_rep(c_j)."""
    n = len(discs); NT = NP.NT
    pts = []
    for a, b, _ in hm:
        for f in np.linspace(0, 1, npts):
            pts.append(tile.zf(a + (b - a)*f))
    rows = []; rhs = []
    # variables: w (NT), mu_i (n), s
    nv = NT + n + 1
    for i, D in enumerate(discs):
        if D.get('kind') == 'iv':
            z = D['zs'][0]; Kz = NP.Kv(z); gz = D['G0f'](z); az = NP.Sf(z); e2 = 0.25*EPS
            for e in (1, -1, 1j, -1j):
                row = np.zeros(nv); row[:NT] = (np.conj(e)*Kz).real; row[NT+i] = -(np.conj(e)*gz).real
                rows.append(row); rhs.append(e2 + (np.conj(e)*az).real)
            continue
        Kc = NP.Kv(D['c']); rho = 0.99*D['r']*np.cos(np.pi/NDIR_IN)
        for k in range(NDIR_IN):
            e = np.exp(-1j*2*np.pi*k/NDIR_IN)
            row = np.zeros(nv); row[:NT] = (e*Kc).real; row[NT+i] = -(e*D['g']).real
            rows.append(row); rhs.append(rho + (e*D['a']).real)
    row = np.zeros(nv); row[:NT] = 1; rows.append(row); rhs.append(tau_w)
    for z in pts:
        g = NP.Gw(z, w_rep)[0]
        if abs(g) < 1e-14: continue
        e = g/abs(g)
        # s <= Re(conj(e) (S(z) - w-hat(z)))  <=>  s + Re(conj(e) w-hat(z)) <= Re(conj(e) S(z))
        Kz = NP.Kv(z); row = np.zeros(nv); row[:NT] = (np.conj(e)*Kz).real; row[-1] = 1
        rows.append(row); rhs.append((np.conj(e)*NP.Sf(z)).real)
    c = np.zeros(nv); c[-1] = -1
    lo = [0.0]*NT + [D['mu0'] for D in discs] + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), lo, hi, key=('baseopt', n, len(pts)))
    if not ok: return None
    return x[:NT]

def install():
    """route the prototype's LPs through the interval-tube versions."""
    NP.rep_lp = rep_lp3
    NP.w1_lp = w1_lp3
    N2.NP.w1_lp = w1_lp3

NEST_PREF = set(x for x in os.environ.get("NEST_PREF", "").split(",") if x); NEST_PREF_W = float(os.environ.get("NEST_PREF_W", "0.25"))
IVSPLIT_MIN = float(os.environ.get("IVSPLIT_MIN", "1e-6")); IVSPLIT_DEPTH = int(os.environ.get("IVSPLIT_DEPTH", "8"))
def solve(discs, tau, tiles, nest, maxnest, tag, log, r_self=0.0, minarc=2**-22, ivdepth=0):
    """as nest2.solve but children use interval tubes; r_self here = the child's arc diameter d (nest deeper only if small)."""
    N2.bump('nodes')
    if N2.STATS['nodes'] > N2.NODE_BUDGET: raise RuntimeError("node budget")
    em = empty_lp3(discs, tau)
    if em is not None and em > 1e-9:
        N2.bump('empty'); log(f"{tag} EMPTY (dual margin {em:.2e})"); return True
    rr = rep_search(discs, tau)
    tau_w = tau
    if rr is not None and tau < rr[2] <= tau*1.01:       # tau_rep: W leaf on the slightly larger set {mass <= tau_w}
        tau_w = rr[2]*(1 + 1e-6) + 1e-12; N2.bump('taurep')
    elif rr is None or rr[2] > tau:
        # ivsplit: refine the widest interval tube's arc locally (the union of the halves covers it); each half must close
        ivs = [(D['d'], i) for i, D in enumerate(discs) if D.get('kind') == 'iv' and D['d'] > IVSPLIT_MIN]
        if ivs and ivdepth < IVSPLIT_DEPTH:
            dmax, i = max(ivs); D = discs[i]; qm = (D['q0'] + D['q1'])/2
            N2.bump('ivsplit')
            for a_, b_ in ((D['q0'], qm), (qm, D['q1'])):
                Dh = iv_disc(D['tile'], a_, b_, D['w0'])
                if not solve(discs[:i] + [Dh] + discs[i+1:], tau, tiles, nest, maxnest, tag + f"|split{i}[{a_:.7f},{b_:.7f}]", log,
                             r_self=r_self, minarc=minarc, ivdepth=ivdepth + 1):
                    return False
            return True
        N2.bump('fail'); N2.bump('norep'); log(f"{tag} FAIL no rep found (min mass {None if rr is None else round(rr[2], 5)})"); return False
    w0 = rr[0]
    odd = [nm for nm, tl in tiles.items() if (lambda n: n is not None and n % 2 == 1)(NP.winding(tl, w0))]
    if not odd:
        N2.bump('fail'); log(f"{tag} FAIL no odd tile"); return False
    lt = N2.LAST_TILE.get(nest)
    pref = ([lt] if lt in odd else []) + [nm for nm in odd if nm != lt]
    for nm in pref:
        iv, nlp, mpos = N2.scan(tiles[nm], (nest, nm), discs, tau_w, N=N2.NFULL, early=True)
        N2.bump('lps', nlp)
        if iv is not None and not iv:
            N2.bump('W'); N2.LAST_TILE[nest] = nm
            log(f"{tag} W {nm} (rep {rr[2]:.5f}, tau_w {tau_w:.5f}, margin {mpos:.2e})"); return True
    if nest >= maxnest or (nest >= 1 and r_self > D_NEST):
        N2.bump('fail'); return False
    best = None
    for nm in pref:
        iv, nlp, mpos = N2.scan(tiles[nm], (nest, nm), discs, tau_w, N=N2.NFULL, early=False)
        N2.bump('lps', nlp)
        hl = sum(b - a for a, b, _ in iv)
        # preference: at nesting level >= 1, zero-5 tiles (NEST_PREF) count as shorter by the factor NEST_PREF_W
        hl_eff = hl*NEST_PREF_W if (nest >= 1 and nm in NEST_PREF) else hl
        if best is None or hl_eff < best[3]: best = (nm, iv, hl, hl_eff)
    nm, hm, hl, _ = best
    log(f"{tag} nest on {nm}: hard {hl:.4f} " + ", ".join(f"[{a:.4f},{b:.4f}]" for a, b, _ in hm[:4]) + f" (rep {rr[2]:.5f})")
    tl = tiles[nm]
    if BASE_OPT:
        wb = base_opt(discs, tau_w, tl, hm, w0)
        if wb is not None:
            nb = NP.winding(tl, wb)
            if nb is not None and nb % 2 == 1:
                g_old = min(abs(NP.Gw(tl.zf((a + b)/2), w0)[0]) for a, b, _ in hm)
                g_new = min(abs(NP.Gw(tl.zf((a + b)/2), wb)[0]) for a, b, _ in hm)
                if g_new > g_old:
                    log(f"{tag}   base optimized: min|G| on hard centres {g_old:.3e} -> {g_new:.3e}"); w0 = wb; N2.bump('baseopt')
    for (a, b, _) in hm:
        stack = [(a, b)]
        while stack:
            q0, q1 = stack.pop()
            D = iv_disc(tl, q0, q1, w0)
            if D['d'] <= DMAX:
                N2.bump('sub')
                if solve(discs + [D], tau, tiles, nest + 1, maxnest, tag + f"/{nm}[{q0:.6f},{q1:.6f}]d{D['d']:.1e}", log, r_self=D['d']):
                    continue
            if q1 - q0 < minarc:
                log(f"{tag}/{nm}[{q0:.8f},{q1:.8f}] FAIL at min width"); return False
            m = (q0 + q1)/2; stack += [(q0, m), (m, q1)]
    return True

DMAX = float(os.environ.get("DMAX", "0.05"))       # largest child arc diameter tried
D_NEST = float(os.environ.get("D_NEST", "0.002"))  # nest deeper only from children at most this wide

# ---- L2-polygon norms: s_v >= |v|_2 via 16 directions (s_v <= |v|_2 / cos(pi/16)), instead of |v|_1 (up to sqrt 2 loss)
NDIR = int(os.environ.get("NDIR", "16"))
_TH = 2*np.pi*np.arange(NDIR)/NDIR
_CP = np.cos(np.pi/NDIR)

def _lp_core(n, NT, p, discs, tau, mode):
    """mode 'w1': variables [u(2), v_i(2)..., eta, s_u, s_i..., m]; mode 'empty': [v_i(2)..., eta, s_i..., m]."""
    nu = 2 if mode == 'w1' else 0
    ncx = (1 if mode == 'w1' else 0) + n                 # complex multipliers
    ie = nu + 2*n; isv = ie + 1; im = isv + ncx; nv = im + 1
    rows = []; rhs = []
    def R(): return np.zeros(nv)
    Kd = [NP.Kv(D['c']) for D in discs]; dk = [dK(D) if D.get('kind') == 'iv' else None for D in discs]
    sidx = lambda i: isv + (1 if mode == 'w1' else 0) + i
    # t rows
    Tm = np.zeros((NT, nv))
    if mode == 'w1':
        Kp = NP.Kv(p); Tm[:, 0] = Kp.real; Tm[:, 1] = Kp.imag
    sg = -1.0 if mode == 'w1' else 1.0
    for i, D in enumerate(discs):
        Tm[:, nu+2*i] = sg*Kd[i].real; Tm[:, nu+2*i+1] = sg*Kd[i].imag
        if dk[i] is not None: Tm[:, sidx(i)] = dk[i]
    Tm[:, ie] = -1
    # sign rows
    Sg = np.zeros((n, nv))
    for i, D in enumerate(discs):
        if mode == 'w1':
            Sg[i, nu+2*i] = D['g'].real; Sg[i, nu+2*i+1] = D['g'].imag
            if D.get('kind') == 'iv': Sg[i, sidx(i)] = D['dG']
        else:
            Sg[i, nu+2*i] = -D['g'].real; Sg[i, nu+2*i+1] = -D['g'].imag
            if D.get('kind') == 'iv': Sg[i, sidx(i)] = D['dG']
    # margin row
    Mg = np.zeros((1, nv))
    if mode == 'w1':
        Sp = NP.Sf(p); Mg[0, 0] = -Sp.real; Mg[0, 1] = -Sp.imag
    for i, D in enumerate(discs):
        bb = D['a'] + D['mu0']*D['g']; rr = D['r'] + (D['dS'] if D.get('kind') == 'iv' else 0.0)
        Mg[0, nu+2*i] = sg*(-1)*bb.real if mode == 'empty' else bb.real
        Mg[0, nu+2*i+1] = sg*(-1)*bb.imag if mode == 'empty' else bb.imag
        Mg[0, sidx(i)] = rr
    Mg[0, ie] = tau; Mg[0, im] = 1
    # norm rows: s >= (re cos th + im sin th)/cp
    Nr = []
    cx = ([(0, isv)] if mode == 'w1' else []) + [(nu+2*i, sidx(i)) for i in range(n)]
    for (j, js) in cx:
        for th in _TH:
            r = R(); r[j] = np.cos(th)/_CP; r[j+1] = np.sin(th)/_CP; r[js] = -1; Nr.append(r)
    Nm = R(); Nm[isv:im] = 1
    A = np.vstack([Tm, Sg, Mg, np.array(Nr), Nm[None, :]])
    b = np.zeros(A.shape[0]); b[-1] = 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(nu + 2*n) + [0.0]*(1 + ncx) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=(mode + '4', n))
    if not ok: return None
    return x, im

def w1_lp4(p, discs, tau):
    r = _lp_core(len(discs), NP.NT, p, discs, tau, 'w1')
    if r is None: return None
    x, im = r
    return complex(x[0], x[1]), x[im]

def empty_lp4(discs, tau):
    r = _lp_core(len(discs), NP.NT, None, discs, tau, 'empty')
    if r is None: return None
    return r[0][r[1]]

def install4():
    NP.rep_lp = rep_lp3
    NP.w1_lp = w1_lp4
    N2.NP.w1_lp = w1_lp4
    global empty_lp3
    empty_lp3 = empty_lp4
