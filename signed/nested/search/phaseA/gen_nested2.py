# Emitter of NESTED certificates with INTERVAL tubes (check_nested.py kind 'iv') for given T1 arcs: float search (nest_proto/nest2 LPs) +
# rational duals verified with the checker's own arb routines before emission (the final verdict is check_nested.py's).
# No box points (pure nesting).  usage: gen_nested.py CFG.json ARCS(k0:k1 or k,k,...) MAXNEST PROCS OUT.jsonl
import numpy as np, sys, os, time, json
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import nest_proto as NP, nest2 as N2, nest3 as N3, check_nested as CN
N3.install4()
import gen_two_level as G2
from flint import acb
import hslp
from multiprocessing import Pool

def rat(x, den=2**50): return Fr(int(round(float(x)*den)), den)
def ratfloor(x, den=2**60): return Fr(int(np.floor(float(x)*den)), den)

# ------------------------------------------------------------------ float LPs with explicit tube list
def empty_lp(discs, tau):
    """max m: sum_i [Re(conj v_i (a_i + mu0_i g_i)) - r_i |v_i|_1] - tau eta >= m, eta >= psi(t) = sum Re(conj v_i K_t(c_i)),
       eta >= 0, Re(conj v_i g_i) >= 0, sum |v_i|_1 <= 1.  Returns ([v_i], m) or None."""
    n = len(discs); NT = NP.NT
    nv = 2*n + 1 + 2*n + 1; ie = 2*n; im = nv - 1
    A = np.zeros((NT + n + 1 + 4*n + 1, nv)); b = np.zeros(A.shape[0]); row = 0
    for i, D in enumerate(discs):
        Kc = NP.Kv(D['c']); A[:NT, 2*i] = Kc.real; A[:NT, 2*i+1] = Kc.imag
    A[:NT, ie] = -1; row = NT
    for i, D in enumerate(discs):
        A[row, 2*i] = -D['g'].real; A[row, 2*i+1] = -D['g'].imag; row += 1
    for i, D in enumerate(discs):
        bb = D['a'] + D['mu0']*D['g']
        A[row, 2*i] = -bb.real; A[row, 2*i+1] = -bb.imag; A[row, ie+1+2*i] = D['r']; A[row, ie+2+2*i] = D['r']
    A[row, ie] = tau; A[row, im] = 1; row += 1
    for j in range(2*n):
        ja = ie + 1 + j
        A[row, j] = 1; A[row, ja] = -1; row += 1
        A[row, j] = -1; A[row, ja] = -1; row += 1
    A[row, ie+1:ie+1+2*n] = 1; b[row] = 1; row += 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(2*n) + [0.0]*(1 + 2*n) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=('empty', n))
    if not ok: return None
    return [complex(x[2*i], x[2*i+1]) for i in range(n)], x[im]

def w1_lp_full(p, discs, tau):
    """as NP.w1_lp but returns all multipliers: (u, [v_i], margin)."""
    n = len(discs); NT = NP.NT
    Kp = NP.Kv(p); Sp = NP.Sf(p)
    ie = 2 + 2*n; nv = ie + 1 + 2 + 2*n + 1; im = nv - 1
    A = np.zeros((NT + n + 1 + 2*(2 + 2*n) + 1, nv)); b = np.zeros(A.shape[0])
    A[:NT, 0] = Kp.real; A[:NT, 1] = Kp.imag
    for i, D in enumerate(discs):
        Kc = NP.Kv(D['c']); A[:NT, 2+2*i] = -Kc.real; A[:NT, 3+2*i] = -Kc.imag
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
    A[row, ie+1:ie+3+2*n] = 1; b[row] = 1
    c = np.zeros(nv); c[im] = -1
    lo = [None]*(2 + 2*n) + [0.0]*(1 + 2 + 2*n) + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, A, b, lo, hi, key=('w1f', n))
    if not ok: return None
    return complex(x[0], x[1]), [complex(x[2+2*i], x[3+2*i]) for i in range(n)], x[im]

# ------------------------------------------------------------------ rigorous helpers
def fix_sign(v, g_ball, sign):
    """shift rational v by sign*c*g' (g' ~ g) so that sign*Re(conj v g) >= 0 holds rigorously."""
    vc = acb(CN.A(v[0]), -CN.A(v[1])); X = (vc*g_ball).real
    if (X >= 0) if sign > 0 else (X <= 0): return v
    gr = rat(float(g_ball.real.mid()), 2**60); gi = rat(float(g_ball.imag.mid()), 2**60)
    xu = abs(float(X.mid())) + float(X.rad())
    c = rat(4*xu/float(gr*gr + gi*gi) + 1e-16, 2**64)
    return (v[0] + sign*c*gr, v[1] + sign*c*gi)

class Arc:
    pass


import contextlib
@contextlib.contextmanager
def tgrid(nt):
    """temporarily switch the LP t-grid (single-threaded worker processes only)."""
    old = (NP.NT, NP.TS)
    NP.NT = nt; NP.TS = np.linspace(-0.5, 0.5, nt)
    try: yield
    finally: NP.NT, NP.TS = old

IV_EPS = Fr(1, 10**6)
NDIR_IN = int(os.environ.get('NDIR_IN', '64'))
NT_EMIT = int(os.environ.get('NT_EMIT', '1601')); NT_FINE = int(os.environ.get('NT_FINE', '4801'))
def iv_float(tb):
    kind, tile, q0, q1, ts, ms = tb
    tsf = np.array([float(t) for t in ts]); msf = np.array([float(m) for m in ms])
    def G0(z): return NP.Sf(z) - np.sum(msf*np.exp(-2j*np.pi*tsf*z))
    def dG0(z): return NP.dSf(z) + np.sum(msf*2j*np.pi*tsf*np.exp(-2j*np.pi*tsf*z))
    qs = np.linspace(float(q0), float(q1), 33); zs = np.array([tile_zf(tile, q) for q in qs]); qc = (q0 + q1)/2; c = tile_zf(tile, qc)
    d = float(np.max(np.abs(zs - c)))*1.02 + 1e-15; Y = float(np.max(np.abs(zs.imag))) + d
    return {'kind': 'iv', 'c': c, 'a': NP.Sf(c), 'g': G0(c), 'mu0': 0.0, 'r': float(IV_EPS),
            'dS': d*float(np.max(np.abs(NP.dSf(zs))))*1.3, 'dG': d*float(max(abs(dG0(z)) for z in zs))*1.3, 'd': d, 'Y': Y,
            'qr_cands': [qc, q0, q1] + [q0 + (q1 - q0)*Fr(i, 8) for i in (1, 3, 2, 6, 5, 7)], 'G0': G0}

def float_discs(ctx, tubes, tau_N):
    r1 = CN.r1_bound(ctx.s0, ctx.s1, ctx.sc, tau_N)
    zc = complex(float(ctx.zc.real.mid()), float(ctx.zc.imag.mid()))
    return [{'c': zc, 'a': 0j, 'g': NP.Sf(zc), 'mu0': 1.0, 'r': float(r1.upper())*(1 + 1e-9)}] + [iv_float(tb) for tb in tubes], r1

def rep_lp_at(discs, qrs, tau_N):
    """min-mass w with the level-1 16-gon (shrink f) and each iv tube crossing at its chosen point."""
    n = len(discs); NT = NP.NT
    for f in (0.9, 0.99, 0.999, 0.9999):
        rows = []; rhs = []
        for i, D in enumerate(discs):
            if D.get('kind') == 'iv':
                tl = D['tile']; z = tile_zf(tl, qrs[i]); Kz = NP.Kv(z); gz = D['G0'](z); az = NP.Sf(z); e2 = 0.25*float(IV_EPS)
                for e in (1, -1, 1j, -1j):
                    row = np.zeros(NT + n); row[:NT] = (np.conj(e)*Kz).real; row[NT+i] = -(np.conj(e)*gz).real
                    rows.append(row); rhs.append(e2 + (np.conj(e)*az).real)
                continue
            Kc = NP.Kv(D['c']); rho = f*D['r']*np.cos(np.pi/NDIR_IN)
            for k in range(NDIR_IN):
                e = np.exp(-1j*2*np.pi*k/NDIR_IN)
                row = np.zeros(NT + n); row[:NT] = (e*Kc).real; row[NT+i] = -(e*D['g']).real
                rows.append(row); rhs.append(rho + (e*D['a']).real)
        c = np.concatenate([np.ones(NT), np.zeros(n)])
        lo = [0.0]*NT + [D['mu0'] for D in discs]; hi = [None]*(NT + n)
        ok, x, fun = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), lo, hi, key=('repat', n))
        if ok and fun <= float(tau_N): return x, fun
    return None

def make_rep2(ctx, discs, tubes, tau_N, r1):
    for i, tb in enumerate(tubes): discs[i+1]['tile'] = tb[1]
    import itertools
    nt = len(discs) - 1
    ranges = [range(3)]*(nt - 1) + [range(9)] if nt >= 1 else []
    for combo in itertools.islice(itertools.product(*ranges), 243):
        qrs = [None] + [discs[i+1]['qr_cands'][j] for i, j in enumerate(combo)]
        r = rep_lp_at(discs, qrs, tau_N)
        if r is None: continue
        x, fun = r; NT = NP.NT
        w = x[:NT]; idx = np.nonzero(w > 1e-14)[0]
        ts = [Fr(-1, 2) + Fr(int(i), NT - 1) for i in idx]; ms = [ratfloor(w[i]) for i in idx]
        if sum(ms) > tau_N: continue
        sigma = max(Fr(1), rat(x[NT], 2**60))
        okr = (CN.what_atoms(ctx.zc, ts, ms) - CN.A(sigma)*ctx.Sc).abs_upper() <= r1
        mus = []
        for k, tb in enumerate(tubes):
            zr = CN.ell_ball(tb[1], qrs[k+1], qrs[k+1])
            res = CN.what_atoms(zr, ts, ms) - CN.S(zr); gr = CN.G_atoms(zr, tb[4], tb[5])
            gm = complex(float(gr.real.mid()), float(gr.imag.mid())); rm = complex(float(res.real.mid()), float(res.imag.mid()))
            mu = max(0.0, (np.conj(gm)*rm).real/abs(gm)**2); muq = rat(mu, 2**60)
            okr = okr and ((res - CN.A(muq)*gr).abs_upper() <= CN.A(IV_EPS))
            mus.append([str(qrs[k+1]), str(muq)])
        if okr: return ts, ms, sigma, mus, w
    return None

def lp_mult(mode, p, discs, tau):
    r = N3._lp_core(len(discs), NP.NT, p, discs, tau, mode)
    if r is None: return None
    x, im = r; n = len(discs); nu = 2 if mode == 'w1' else 0
    u = complex(x[0], x[1]) if mode == 'w1' else None
    return u, [complex(x[nu+2*i], x[nu+2*i+1]) for i in range(n)], x[im]

def fix_iv(vq, tb, sign):
    """make the interval-tube sign condition hold rigorously by shifting vt along sign*G_base(centre)."""
    if CN.iv_bounds(tb, vq, sign, None)[0]: return vq
    kind, tile, q0, q1, ts, ms = tb; qc = (q0 + q1)/2
    g = CN.G_atoms(CN.ell_ball(tile, qc, qc), ts, ms); gr = rat(float(g.real.mid()), 2**60); gi = rat(float(g.imag.mid()), 2**60)
    nv = (float(vq[0])**2 + float(vq[1])**2)**0.5; ng = (float(gr)**2 + float(gi)**2)**0.5 + 1e-300
    for c in (1e-9, 1e-7, 1e-5, 1e-4, 1e-3, 1e-2):
        k = rat(c*nv/ng, 2**64); v2 = (vq[0] + sign*k*gr, vq[1] + sign*k*gi)
        if CN.iv_bounds(tb, v2, sign, None)[0]: return v2
    return None

def emit_w1(ctx, tile, q0, q1, discs, tubes, tau_N, r1, cache, maxsub=2**-14):
    out = []; bad = []; todo = [(q0, q1, 0)]
    while todo:
        a, b, fine = todo.pop()
        p = tile_zf(tile, (a + b)/2)
        with tgrid(NT_FINE if fine else NT_EMIT): d = lp_mult('w1', p, discs, float(tau_N))
        if d is None or d[2] <= 1e-7:
            bump('w1_lp_nonpos'); bad.append((a, b)); continue
        u, vs, mg = d
        uq = (rat(u.real), rat(u.imag)); vq = [(rat(v.real), rat(v.imag)) for v in vs]
        vq[0] = fix_sign(vq[0], ctx.Sc, -1); okf = True
        for k in range(1, len(vq)):
            vq[k] = fix_iv(vq[k], tubes[k-1], -1)
            if vq[k] is None: okf = False; bump('w1_fixiv_fail'); break
        if okf and not CN.check_w1_arc(ctx, tile, a, b, [], tubes, uq, vq[0], [], vq[1:], tau_N, r1, cache):
            bump('w1_rig_fail_d%d' % min(len(tubes), 2)); okf = False
            if DIAG and STATS.get('diag', 0) < DIAG and tubes:
                bump('diag'); print(f"  DIAG arc [{float(a):.6f},{float(b):.6f}] LP margin {mg:.3e}: " + CN.diag_w1_arc(ctx, tile, a, b, [], tubes, uq, vq[0], [], vq[1:], tau_N, r1, cache), flush=True)
        if okf:
            out.append([str(a), str(b), str(uq[0]), str(uq[1]), str(vq[0][0]), str(vq[0][1])] + [str(x) for v in vq[1:] for x in v])
            continue
        if b - a <= maxsub:
            if not fine: todo.append((a, b, 1)); bump('fine_retry'); continue
            bad.append((a, b)); continue
        m = (a + b)/2; todo += [(a, m, fine), (m, b, fine)]
    return out, bad

def try_empty(ctx, discs, tubes, tau_N, cache, fine=False):
    with tgrid(NT_FINE if fine else NT_EMIT): e = lp_mult('empty', None, discs, float(tau_N))
    if e is None or e[2] <= 1e-9: return None
    vq = [(rat(v.real), rat(v.imag)) for v in e[1]]
    vq[0] = fix_sign(vq[0], ctx.Sc, +1)
    for k in range(1, len(vq)):
        vq[k] = fix_iv(vq[k], tubes[k-1], +1)
        if vq[k] is None: return None
    lf = {"boxes": [], "type": "empty", "v": [str(vq[0][0]), str(vq[0][1])], "y": [], "vt": [[str(a), str(b)] for a, b in vq[1:]]}
    if CN.check_empty(ctx, [], tubes, lf, cache) is None: return lf
    if not fine:
        bump('fine_retry_empty'); return try_empty(ctx, discs, tubes, tau_N, cache, fine=True)
    return None

def tile_zf(tile, q):
    cr, ci, a, b = tile
    q = float(q)
    return float(cr) + float(a)*np.cos(2*np.pi*q) + 1j*(float(ci) + float(b)*np.sin(2*np.pi*q))

class FTile:
    def __init__(self, t):
        self.t = t; self.f = tuple(float(x) for x in t)
    def zf(self, q):
        cr, ci, a, b = self.f
        q = np.asarray(q, dtype=float)
        return cr + a*np.cos(2*np.pi*q) + 1j*(ci + b*np.sin(2*np.pi*q))

STATS = {}
def bump(k, v=1): STATS[k] = STATS.get(k, 0) + v
DMAX = float(os.environ.get("DMAX", "0.05")); D_NEST = float(os.environ.get("D_NEST", "0.002"))

DBG = os.environ.get("DEBUG")
DIAG = int(os.environ.get("DIAG", "0"))
T00 = time.time()
def dbg(msg):
    if DBG: print(f"  [{time.time()-T00:7.1f}s] {msg}", file=sys.stderr, flush=True)

NEST_PREF = set(x for x in os.environ.get("NEST_PREF", "T5,T5Lm,T5Lp,T5b").split(",") if x)
NEST_PREF_W = float(os.environ.get("NEST_PREF_W", "0.25"))
IVSPLIT_MIN = float(os.environ.get("IVSPLIT_MIN", "1e-6")); IVSPLIT_DEPTH = int(os.environ.get("IVSPLIT_DEPTH", "8"))
BASE_OPT = int(os.environ.get("BASE_OPT", "1"))

def arc_diam(tile, q0, q1):
    zs = [tile_zf(tile, q0), tile_zf(tile, q1), tile_zf(tile, (q0 + q1)/2)]
    return max(abs(z1 - z2) for z1 in zs for z2 in zs)

def base_rep(ctx, discs, tubes, tau_W, r1, tile, hard, qrs, w_old):
    """a representative in E_N (verified like make_rep2) maximizing min_j Re(conj(e_j) G_w(c_j)) over points of the hard
    intervals, e_j = direction of G_old(c_j); used as the base of the hard-arc tubes (Lemma X allows any odd base in C_N)."""
    n = len(discs); NT = NP.NT
    pts = []
    for a, b in hard:
        for f in (Fr(0), Fr(1, 2), Fr(1)):
            pts.append(tile_zf(tile, a + (b - a)*f))
    nv = NT + n + 1; rows = []; rhs = []
    for i, D in enumerate(discs):
        if D.get('kind') == 'iv':
            tl = D['tile']; z = tile_zf(tl, qrs[i]); Kz = NP.Kv(z); gz = D['G0'](z); az = NP.Sf(z); e2 = 0.25*float(IV_EPS)
            for e in (1, -1, 1j, -1j):
                row = np.zeros(nv); row[:NT] = (np.conj(e)*Kz).real; row[NT+i] = -(np.conj(e)*gz).real
                rows.append(row); rhs.append(e2 + (np.conj(e)*az).real)
            continue
        Kc = NP.Kv(D['c']); rho = 0.99*D['r']*np.cos(np.pi/NDIR_IN)
        for k in range(NDIR_IN):
            e = np.exp(-1j*2*np.pi*k/NDIR_IN)
            row = np.zeros(nv); row[:NT] = (e*Kc).real; row[NT+i] = -(e*D['g']).real
            rows.append(row); rhs.append(rho + (e*D['a']).real)
    row = np.zeros(nv); row[:NT] = 1; rows.append(row); rhs.append(float(tau_W)*(1 - 1e-9))
    for z in pts:
        g = NP.Sf(z) - np.sum(w_old*np.exp(-2j*np.pi*NP.TS*z))
        if abs(g) < 1e-14: continue
        e = g/abs(g); Kz = NP.Kv(z)
        row = np.zeros(nv); row[:NT] = (np.conj(e)*Kz).real; row[-1] = 1; rows.append(row); rhs.append((np.conj(e)*NP.Sf(z)).real)
    c = np.zeros(nv); c[-1] = -1
    lo = [0.0]*NT + [D['mu0'] for D in discs] + [None]; hi = [None]*nv
    ok, x, fun = hslp.solve_ub(c, np.array(rows), np.array(rhs, float), lo, hi, key=('baserep', n, len(pts)))
    if not ok: return None
    w = x[:NT]; idx = np.nonzero(w > 1e-14)[0]
    ts = [Fr(-1, 2) + Fr(int(i), NT - 1) for i in idx]; ms = [ratfloor(w[i]) for i in idx]
    if sum(ms) > tau_W: return None
    sigma = max(Fr(1), rat(x[NT], 2**60))
    if not ((CN.what_atoms(ctx.zc, ts, ms) - CN.A(sigma)*ctx.Sc).abs_upper() <= r1): return None
    mus = []
    for k_, tb in enumerate(tubes):
        q = qrs[k_+1]; zr = CN.ell_ball(tb[1], q, q)
        res = CN.what_atoms(zr, ts, ms) - CN.S(zr); gr = CN.G_atoms(zr, tb[4], tb[5])
        gm = complex(float(gr.real.mid()), float(gr.imag.mid())); rm = complex(float(res.real.mid()), float(res.imag.mid()))
        mu = max(0.0, (np.conj(gm)*rm).real/abs(gm)**2); muq = rat(mu, 2**60)
        if not ((res - CN.A(muq)*gr).abs_upper() <= CN.A(IV_EPS)): return None
        mus.append([str(q), str(muq)])
    return ts, ms, sigma, mus, w

def search(ctx, tubes, nest, maxnest, cache, tau_N, d_self=0.0, ivdepth=0, stub_root=False):
    bump('nodes'); dbg(f"node nest={nest} tubes={[(float(t[2]), float(t[3])) for t in tubes]}")
    if STATS['nodes'] > int(os.environ.get("NODE_BUDGET", "20000")): raise RuntimeError("node budget")
    discs, r1 = float_discs(ctx, tubes, tau_N)
    lf = try_empty(ctx, discs, tubes, tau_N, cache)
    if lf is not None: bump('empty'); return lf
    rep = make_rep2(ctx, discs, tubes, tau_N, r1)
    tau_W = tau_N
    if rep is None:                      # tau_rep: a W leaf on the slightly larger set {mass <= tau_W}
        for tr in (tau_N*Fr(2001, 2000), tau_N*Fr(501, 500), tau_N*Fr(101, 100)):
            dW, r1W = float_discs(ctx, tubes, tr)
            rep = make_rep2(ctx, dW, tubes, tr, r1W)
            if rep is not None:
                tau_W, discs, r1 = tr, dW, r1W; bump('taurep'); break
    if rep is None:
        # ivsplit (the arc splits of the paper): refine the widest interval tube's arc locally; both halves must close
        cand = [(arc_diam(tb[1], tb[2], tb[3]), k) for k, tb in enumerate(tubes) if tb[0] == "iv"]
        cand = [(d_, k) for d_, k in cand if d_ > IVSPLIT_MIN]
        if cand and ivdepth < IVSPLIT_DEPTH:
            d_, k = max(cand); kind, tl, q0, q1, bts, bms = tubes[k]; qm = (q0 + q1)/2
            kids = []
            for a_, b_ in ((q0, qm), (qm, q1)):
                t2 = list(tubes); t2[k] = ("iv", tl, a_, b_, bts, bms)
                kid = search(ctx, t2, nest, maxnest, cache, tau_N, d_self=d_self, ivdepth=ivdepth + 1)
                if kid is None: bump('ivsplit_fail'); return None
                kids.append(kid)
            bump('ivsplit')
            return {"ivsplit": k, "at": str(qm), "kids": kids}
        bump('norep'); dbg("  no rep"); return None
    ts, ms, sigma, mus, wf = rep
    tiles = ctx.tiles
    odd = [nm for nm in tiles if (lambda n: n is not None and n % 2 == 1)(NP.winding(FTile(tiles[nm]), wf))]
    lt = ctx.last.get(nest)
    pref = ([lt] if lt in odd else []) + [nm for nm in odd if nm != lt]
    def finish(nm, arcs, ts, ms, sigma, mus):
        n = CN.winding(tiles[nm], ts, ms)
        if n is None or n % 2 == 0: return None
        return {"boxes": [], "type": "W", "tile": nm, "tau_rep": str(tau_W), "tile_arcs": arcs, "wrep_t": [str(t) for t in ts],
                "wrep_m": [str(x) for x in ms], "sigma": str(sigma), "mus": mus}
    for nm in pref:
        iv, nlp, mpos = N2.scan(FTile(tiles[nm]), (nest, nm), discs, float(tau_W), N=512, early=True)
        if iv is None or iv: continue
        arcs, bad = [], []
        for k in range(64):
            o, bd = emit_w1(ctx, tiles[nm], Fr(k, 64), Fr(k + 1, 64), discs, tubes, tau_W, r1, cache)
            arcs += o; bad += bd
            if bad: break
        if bad: continue
        lf = finish(nm, arcs, ts, ms, sigma, mus)
        if lf is not None:
            ctx.last[nest] = nm; bump('W'); return lf
    if nest >= maxnest or (nest >= 1 and d_self > D_NEST): return None
    best = None
    for nm in pref:
        iv, nlp, mpos = N2.scan(FTile(tiles[nm]), (nest, nm), discs, float(tau_W), N=512, early=False)
        hl = sum(b - a for a, b, _ in iv)
        hl_eff = hl*NEST_PREF_W if (nest >= 1 and nm[:-2] in NEST_PREF) else hl
        if best is None or hl_eff < best[3]: best = (nm, iv, hl, hl_eff)
    if best is None: return None
    nm, iv, hl, _ = best
    dbg(f"  nest on {nm}: hard {hl:.4f} {[(round(a,4), round(b,4)) for a, b, _ in iv][:4]}")
    tile = tiles[nm]
    hard_cells = set()
    for a, b, _ in iv:
        for k in range(int(round(a*512)), int(round(b*512))): hard_cells.add(k)
    arcs = []; hard = []
    for k in range(512):
        a, b = Fr(k, 512), Fr(k + 1, 512)
        if k in hard_cells: hard.append((a, b)); continue
        o, bd = emit_w1(ctx, tile, a, b, discs, tubes, tau_W, r1, cache)
        arcs += o; hard += bd
    hard.sort(); dbg(f"  W1 emitted on non-hard cells: {len(arcs)} arcs, {len(hard)} hard cells")
    merged = []
    for a, b in hard:
        if merged and merged[-1][1] == a: merged[-1] = (merged[-1][0], b)
        else: merged.append((a, b))
    if BASE_OPT and merged:      # a better base for the tubes: same node set, larger |G| on the hard arcs, odd on the tile
        qrs = [None] + [Fr(mu[0]) for mu in mus]
        br = base_rep(ctx, discs, tubes, tau_W, r1, tile, merged, qrs, wf)
        if br is not None:
            nb = CN.winding(tile, br[0], br[1])
            if nb is not None and nb % 2 == 1:
                g_old = min(abs(NP.Sf(tile_zf(tile, (a + b)/2)) - np.sum(wf*np.exp(-2j*np.pi*NP.TS*tile_zf(tile, (a + b)/2)))) for a, b in merged)
                g_new = min(abs(NP.Sf(tile_zf(tile, (a + b)/2)) - np.sum(br[4]*np.exp(-2j*np.pi*NP.TS*tile_zf(tile, (a + b)/2)))) for a, b in merged)
                if g_new > g_old:
                    ts, ms, sigma, mus, wf = br; bump('baseopt')
    if stub_root and nest == 0:     # production phase A: return the root W leaf without its hard children
        return {"stub": True, "boxes": [], "type": "W", "tile": nm, "tau_rep": str(tau_W), "w1_arcs": arcs,
                "hard": [[str(a), str(b)] for a, b in merged], "wrep_t": [str(t) for t in ts], "wrep_m": [str(x) for x in ms],
                "sigma": str(sigma), "mus": mus}
    for a, b in merged:
        stack = [(a, b)]
        while stack:
            x, y = stack.pop()
            tb = ("iv", tile, x, y, tuple(ts), tuple(ms))
            dd = arc_diam(tile, x, y)
            child = None
            if dd <= DMAX:
                bump('sub')
                child = search(ctx, tubes + [tb], nest + 1, maxnest, cache, tau_N, d_self=dd)
            if child is not None:
                arcs.append({"hard": [str(x), str(y)], "kind": "iv", "child": child}); continue
            if y - x < Fr(1, 2**22): return None
            m = (x + y)/2; stack += [(x, m), (m, y)]
    lf = finish(nm, arcs, ts, ms, sigma, mus)
    if lf is not None: bump('Wnest')
    return lf

G = {}
def init(g): G.update(g); CN.G.update(g["cn"])

def do_arc(k):
    """k = fine index (nH = 4096) or a string 's0/s1' pair "a/b:c/d" (refined arcs)."""
    STATS.clear(); t0 = time.time()
    nH = G["nH"]
    if isinstance(k, str):
        a, b = k.split(":"); s0, s1 = Fr(a), Fr(b)
    else:
        s0, s1 = Fr(k, nH), Fr(k + 1, nH)
    sc = (s0 + s1)/2
    tau = G["cn"]["tau"]
    T1 = G2.Ell((G["cn"]["T1"][0], Fr(0)), G["cn"]["T1"][2], G["cn"]["T1"][3])
    rE = G2.solve_E((T1, s0, s1, tau))
    if rE is not None: return k, rE, {"E": 1}, time.time() - t0
    ctx = Arc(); ctx.s0, ctx.s1, ctx.sc = s0, s1, sc
    ctx.zc = CN.ell_ball(G["cn"]["T1"], sc, sc); ctx.Sc = CN.S(ctx.zc); ctx.pcs = []; ctx.kc = {}
    up = float(ctx.zc.imag.mid()) >= 0
    ctx.tiles = {nm: t for nm, t in G["cn"]["tiles"].items() if nm.endswith("up" if up else "dn")}; ctx.last = {}
    try:
        root = search(ctx, [], 0, G["maxnest"], {}, tau)
    except RuntimeError as e:
        root = None; STATS['budget'] = 1
    if root is None: return k, {"fail": True, "s0": str(s0)}, dict(STATS), time.time() - t0
    return k, {"type": "N", "s0": str(s0), "s1": str(s1), "sc": str(sc), "pcs": [], "Rs": [], "tree": root}, dict(STATS), time.time() - t0

def do_coarse_E(j):
    nE = G["nE"]; s0, s1 = Fr(j, nE), Fr(j + 1, nE); tau = G["cn"]["tau"]
    T1 = G2.Ell((G["cn"]["T1"][0], Fr(0)), G["cn"]["T1"][2], G["cn"]["T1"][3])
    return j, G2.solve_E((T1, s0, s1, tau))

if __name__ == "__main__":
    # modes:  gen_nested2.py CFG SPEC MAXNEST PROCS OUT.jsonl      SPEC = "k0:k1" | "k,k,..." (fine arcs, nH = 4096)
    #         gen_nested2.py CFG all:SHARD/NSHARDS MAXNEST PROCS OUT.jsonl   (coarse E pass over nE = 512, then the fine arcs of
    #         the non-E coarse arcs whose index % NSHARDS == SHARD; resumable: arcs already in OUT.jsonl are skipped)
    cfg = json.load(open(sys.argv[1])); spec = sys.argv[2]; maxnest = int(sys.argv[3]); procs = int(sys.argv[4]); out = sys.argv[5]
    tau = Fr(os.environ.get("TAU", cfg["tau"]))
    c, a_, b_ = (Fr(x) for x in cfg["T1"])
    tiles = {}
    for nm, t in cfg["tiles"].items():
        tiles[nm + "up"] = (Fr(t[0]), Fr(t[1]), Fr(t[2]), Fr(t[3])); tiles[nm + "dn"] = (Fr(t[0]), -Fr(t[1]), Fr(t[2]), Fr(t[3]))
    g = {"nH": 4096, "nE": 512, "maxnest": maxnest, "cn": {"tau": tau, "T1": (c, Fr(0), a_, b_), "tiles": tiles, "iv_eps": IV_EPS}}
    t0 = time.time()
    done = set()
    if os.path.exists(out):
        for l in open(out):
            r = json.loads(l)
            if "k" in r and "fail" not in r["result"]: done.add(("f", r["k"]))
            if "j" in r: done.add(("c", r["j"]))
    J = open(out, "a")
    with Pool(procs, initializer=init, initargs=(g,)) as pool:
        open(out + ".pid", "w").write(f"{os.getpid()}\n")
        if spec.startswith("all:"):
            shard, nsh = (int(x) for x in spec[4:].split("/"))
            coarse = [j for j in range(512) if ("c", j) not in done]
            Eres = {}
            if os.path.exists(out):
                for l in open(out):
                    r = json.loads(l)
                    if "j" in r: Eres[r["j"]] = r["result"]
            for j, rE in pool.imap_unordered(do_coarse_E, coarse, chunksize=4):
                Eres[j] = rE
                if shard == 0:
                    J.write(json.dumps({"j": j, "result": rE}) + "\n"); J.flush()
            hard = sorted(j for j, r in Eres.items() if r is None)
            ks = [k for idx, j in enumerate(hard) if idx % nsh == shard for k in range(8*j, 8*j + 8) if ("f", k) not in done]
            print(f"[{time.time()-t0:7.1f}s] coarse E arcs {sum(1 for r in Eres.values() if r is not None)}/512; shard {shard}/{nsh}: {len(ks)} fine arcs to do", flush=True)
        elif spec.startswith("ref:"):
            ks = []
            for item in spec[4:].split(","):
                kk, parts = item.split("x"); kk, parts = int(kk), int(parts)
                for i in range(parts):
                    a_s = Fr(kk, 4096) + Fr(i, 4096*parts); b_s = Fr(kk, 4096) + Fr(i + 1, 4096*parts)
                    ks.append(f"{a_s}:{b_s}")
        elif ":" in spec:
            a, b = spec.split(":"); ks = [k for k in range(int(a), int(b)) if ("f", k) not in done]
        else:
            ks = [int(x) for x in spec.split(",") if ("f", int(x)) not in done]
        for k, res, st, dt in pool.imap_unordered(do_arc, ks, chunksize=1):
            J.write(json.dumps({"k": k, "result": res, "stats": st, "dt": dt}) + "\n"); J.flush()
            print(f"[{time.time()-t0:7.1f}s] arc {k}: {'FAIL' if 'fail' in res else res.get('type')} {st} {dt:.0f}s", flush=True)
