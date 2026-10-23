#!/usr/bin/env python3
"""indep_nested.py: second checker for NESTED zero-parity certificates (signed third autocorrelation, variant C').

Origin: written separately from check_nested.py, but not independently of it. The first version (2026-10-21) was written
after reading the conditions of Section 6 of the paper, the full code of check_nested.py (version f263f84a) and
gen_nested2.py; the arc-split (ivsplit) branch was added after reading check_nested.py's ivsplit code, and the --deep
scheduling after reading check_nested.py's --deep code (version 82b051f4). Nothing is imported from check_nested.py or
gen_nested2.py. 36 source lines of at least 25 characters coincide with check_nested.py 82b051f4 (23 verbatim, 13 after
renaming identifiers): reading of certificate fields; format and structure checks (multiplier counts, the tiling of [0, 1]
by the tile arcs, split-node boxes, root boxes, the odd-winding test); the H-arc tree set-up; error strings; and two
one-line steps inside numerical routines (a bisection push in the t-sweep and the winding-number integrality test
|w - n| < 1/4). The numerics were written separately: the enclosures of S, S', S'', K_t and G, the extrema over arcs,
the t-sweep, the level-1 radius r1, the winding computation (apart from that one line), the interval-tube bounds, the box
extrema and the E-arc test share no code with check_nested.py.

Notation: S(z) = sin(pi z)/(pi z), K_t(z) = exp(-2 pi i t z), w^(z) = int w K_t(z) dt, G_w = S - w^,
W_tau = {w >= 0 measure on [-1/2,1/2], int w <= tau}. Ellipses (cr, ci, a, b): z(q) = cr + a cos 2 pi q + i(ci + b sin 2 pi q).

What is verified (fail-closed: a missing or malformed field that a check reads, an unsupported kind or type, or an
unexpected node structure rejects the arc; fields that no check reads are ignored):
 global  T1 = (c, a, b), c real: exactly one integer n != 0 with c - a < n < c + a, and c +- a are not integers (S != 0 on
         T1); the T1 arcs [s0, s1] tile [0, 1]; 0 < tau < 1; 0 <= eps <= 1/1000.
 E arc   (u): for every z on the arc and t in [-1/2,1/2]: Re(conj u S(z)) > 0 and tau Re(conj u K_t(z)) < Re(conj u S(z)).
 rooted  (N / H3 / H) arc [s0, s1] with centre zc = z_T1(sc): root boxes Q_j = [-R_j, R_j]^2 with R_j >= tau e^{pi |Im p_j|};
         a node with boxes Qs and interval tubes (A_k, base atoms of G_k) has
           E_N = {w in W_{tau_N}: exists sigma >= 1 with |w^(zc) - sigma S(zc)| <= r1; w^(p_j) in Q_j; for every tube k
                  exists z in A_k, mu >= 0 with |w^(z) - S(z) - mu G_k(z)| <= eps},   C_N = conv(E_N).
         r1 must be at least the level-1 localisation bound d (tau_N pi e^{pi Y} + sigma_max sup|S'|) (Lemma 6.5). Two valid
         versions are computed here: r1_disc (disc of radius d = vmax*max(s1 - sc, sc - s0) around zc) and r1_box (the exact
         bounding box of the arc). r1_valid = min(r1_disc, r1_box). Empty leaves use r1_valid. A W leaf uses
         r1_N = max(r1_valid, |w_rep^(zc) - sigma S(zc)|), so that w_rep is in E_N, every relevant w is in E_N, and all its
         separation bounds use the same r1_N.
 empty   (v, y_j, vt_k): Re(conj v S(zc)) >= 0; Re(conj vt_k G_k) >= 0 on A_k; with
           L = Re(conj v S(zc)) - |v| r1 + sum_j min_{Q_j} Re(conj y_j x) + sum_k [inf_{A_k} Re(conj vt_k S) - |vt_k| eps]:
           L > 0 and tau_N sup_t psi < L, where psi(t) = Re(conj v K_t(zc)) + sum_j Re(conj y_j K_t(p_j))
           + sum_k sup_{z in A_k} Re(conj vt_k K_t(z))   =>  E_N is empty.
 W leaf  w_rep = sum m_i delta_{t_i} (m_i >= 0, t_i in [-1/2,1/2], sum m_i <= tau_N, tau <= tau_N < 1), sigma >= 1, the
         crossing disc, the boxes, and for every tube a point q_r in [q0, q1] and mu_r >= 0 with
         |w_rep^(z(q_r)) - S(z(q_r)) - mu_r G_k(z(q_r))| <= eps (so w_rep is in E_N); the winding number of G_{w_rep} along
         the tile is odd (G_{w_rep} != 0 on the tile); the tile arcs tile [0, 1]; each is
           W1 [q0, q1, u, v, y_j, vt_k]: Re(conj v S(zc)) <= 0, Re(conj vt_k G_k) <= 0 on A_k, and for every p on the arc
             Re(conj u S(p)) - B > tau_N max(0, sup_t phi_p(t)), with
             B = Re(conj v S(zc)) + |v| r1_N + sum_j max_{Q_j} Re(conj y_j x) + sum_k [sup_{A_k} Re(conj vt_k S) + |vt_k| eps],
             phi_p(t) = Re(conj u K_t(p)) - Re(conj v K_t(zc)) - sum_j Re(conj y_j K_t(p_j))
                        + sum_k sup_{z in A_k} Re(-conj vt_k K_t(z));
           hard {"hard": [q0, q1], "kind": "iv", "child": node}: the child node has the same boxes and the tube list extended
             by (this tile arc, base w_rep of this leaf).
         ("disc" tubes, which the paper does not use, are NOT supported here and reject the arc.)
 ivsplit {"ivsplit": k, "at": qm, "kids": [lo, hi]} (the arc splits of the paper): k (an int, not a
         bool) indexes the node's tube list root-first; tube k's arc [q0, q1] must satisfy q0 < qm < q1 (qm read as an
         exact rational); kid lo is checked with tube k restricted to [q0, qm], kid hi with [qm, q1] (same ellipse, same
         base atoms, same boxes, same nesting level); both kids must pass. Sound since E_N = E_lo u E_hi (the crossing
         point of tube k lies in one closed half).
The paper (induction over w in E_N n W_tau, with the convex hull used only for w_{s*} and for separation/emptiness)
then gives: every w in W_tau has a zero of odd multiplicity, hence ess sup f*f > (int f)^2 / (1 - tau).

Numerics (methods chosen separately from check_nested.py's): python-flint arb at 128 bits; S = acb.sinc_pi, S' = (cos pi z - S)/z,
S'' = -pi^2 S - 2 S'/z, K_t(z) = exp_pi_i(-2 t z); an ellipse arc q in [q0, q1] lies in the disc D(z(qm), vmax h),
h = (q1 - q0)/2, vmax = 2 pi max(a, b); extrema of g(q) = Re(c f(z(q))) over arcs by second-order Taylor forms
|g''| <= |c| (sup|f''| vmax^2 + sup|f'| amax) with branch and bound; t-maximisation by the mean-value form
phi(t) <= phi(tm) + h_t sup|d phi/dt| on dyadic t-cells (adaptive, depth <= 34); winding numbers from values on
sub-arcs certified to stay in a disc avoiding 0 (|G(zm)| > 2 rho sup|G'|).

Usage: python3 -I -B indep_nested.py CERT.json[.gz] NPROC OUT.jsonl [--arcs=i,j,...] [--subset] [--deep]
  --arcs: these arcs only, no coverage claim;  --subset: every arc of the file, no coverage claim;
  --deep (the conditions are unchanged, only their scheduling): pass 1 checks
  each arc with the subtrees below the hard tile arcs of a ROOT W leaf left out (their indices are returned); pass 2 checks
  each such subtree as a separate job, exactly as check_W does (same arc context and root boxes, tube list [(root tile,
  [q0, q1], root w_rep)], nesting level 1). An arc passes iff pass 1 and all its pass-2 jobs pass. Job records go to
  OUT.jsonl.jobs.
"""
import sys, os, json, gzip, time
from fractions import Fraction as F
import flint
from flint import arb, acb, fmpq

PREC = 128
flint.ctx.prec = PREC
PI = arb.pi()
I1 = acb(0, 1)
TMAXDEPTH = 34          # smallest t-cell 2^-34
CELL_BUDGET = 2_000_000 # per t-sweep (safety net; a failing sweep normally stops at the first cell of depth TMAXDEPTH)
W1_PDEPTH = 6           # bisections of a W1 tile arc (same multipliers)
E_DEPTH = 8             # bisections of an E arc
NSUBS = (4, 16, 64)     # sub-pieces of arc terms at the t-midpoint (retries with 16, 64)


def ar(x):
    x = F(x)
    return arb(fmpq(x.numerator, x.denominator))


def cpl(p):
    if not (isinstance(p, (list, tuple)) and len(p) == 2):
        raise ValueError("complex pair expected")
    return F(p[0]), F(p[1])


def conjb(p):
    return acb(ar(p[0]), -ar(p[1]))


def modb(p):
    return (ar(p[0]) ** 2 + ar(p[1]) ** 2).sqrt()


def amax_(x, y):
    return x if y is None else (y if x is None else x.max(y))


# ------------------------------------------------------------------ special functions
def S0(z):
    return z.sinc_pi()


def S1(z):
    return (z.cos_pi() - z.sinc_pi()) / z


def S2(z):
    return -PI * PI * z.sinc_pi() - 2 * S1(z) / z


def Kt(t, z):
    return (-2 * t * z).exp_pi_i()


class Atoms:
    """w = sum m_i delta_{t_i}: w^, G_w and its first two derivatives."""
    def __init__(self, ts, ms):
        self.ts = tuple(F(x) for x in ts); self.ms = tuple(F(x) for x in ms)
        self.t = [ar(x) for x in self.ts]; self.m = [ar(x) for x in self.ms]

    def what(self, z):
        s = acb(0)
        for t, m in zip(self.t, self.m):
            s += m * Kt(t, z)
        return s

    def G0(self, z):
        return S0(z) - self.what(z)

    def G1(self, z):
        s = S1(z)
        for t, m in zip(self.t, self.m):
            s += m * 2 * PI * I1 * t * Kt(t, z)
        return s

    def G2(self, z):
        s = S2(z)
        for t, m in zip(self.t, self.m):
            s += m * 4 * PI * PI * t * t * Kt(t, z)
        return s


SFUN = (S0, S1, S2)


class Ell:
    """z(q) = cr + a cos(2 pi q) + i (ci + b sin(2 pi q)), q in [0, 1], counter-clockwise."""
    def __init__(self, cr, ci, a, b):
        self.cr, self.ci, self.a, self.b = F(cr), F(ci), F(a), F(b)
        if not (self.a > 0 and self.b > 0):
            raise ValueError("ellipse axes must be positive")
        self.CR, self.CI, self.A, self.B = ar(self.cr), ar(self.ci), ar(self.a), ar(self.b)
        mx = ar(max(self.a, self.b))
        self.vmax = (2 * PI * mx).upper()          # sup |z'(q)|
        self.amax = (4 * PI * PI * mx).upper()     # sup |z''(q)|
        self._cs = {}

    def cs(self, q):
        v = self._cs.get(q)
        if v is None:
            x = 2 * F(q)
            f = fmpq(x.numerator, x.denominator)
            v = (arb.cos_pi_fmpq(f), arb.sin_pi_fmpq(f))
            if len(self._cs) < 200000:
                self._cs[q] = v
        return v

    def z(self, q):
        c, s = self.cs(q)
        return acb(self.CR + self.A * c, self.CI + self.B * s)

    def dz(self, q):
        c, s = self.cs(q)
        return 2 * PI * acb(-self.A * s, self.B * c)

    def piece(self, q0, q1):
        """(qm, h, z(qm), z'(qm), box, rho): z([q0, q1]) lies in the disc D(z(qm), rho), rho = vmax h, and box contains it."""
        q0, q1 = F(q0), F(q1)
        qm = (q0 + q1) / 2; h = (q1 - q0) / 2
        zm = self.z(qm)
        rho = (self.vmax * ar(h)).upper()
        box = acb(zm.real + arb(0, rho), zm.imag + arb(0, rho))
        return qm, h, zm, self.dz(qm), box, rho


# ------------------------------------------------------------------ extrema along arcs (second-order forms)
def g_bounds(ell, q0, q1, c, fs):
    """(lower, upper, g(qm)) for g(q) = Re(c f(z(q))) on [q0, q1]."""
    f0, f1, f2 = fs
    qm, h, zm, dzm, box, rho = ell.piece(q0, q1)
    gm = (c * f0(zm)).real
    g1 = (c * f1(zm) * dzm).real
    M2 = c.abs_upper() * (f2(box).abs_upper() * ell.vmax * ell.vmax + f1(box).abs_upper() * ell.amax)
    H = ar(h)
    e = H * g1.abs_upper() + H * H / 2 * M2
    return (gm - e).lower(), (gm + e).upper(), gm


def arc_sign(ell, q0, q1, c, fs, sign, n0=4, dmax=22):
    """True iff sign * Re(c f(z(q))) >= 0 for all q in [q0, q1] is certified."""
    q0, q1 = F(q0), F(q1)
    stack = [(q0 + (q1 - q0) * F(i, n0), q0 + (q1 - q0) * F(i + 1, n0), 0) for i in range(n0)]
    while stack:
        a, b, d = stack.pop()
        lo, hi, gm = g_bounds(ell, a, b, c, fs)
        if (lo >= 0) if sign > 0 else (hi <= 0):
            continue
        if (gm < 0) if sign > 0 else (gm > 0):
            return False                                   # violated at the midpoint
        if d >= dmax:
            return False
        m = (a + b) / 2
        stack += [(a, m, d + 1), (m, b, d + 1)]
    return True


def arc_sup(ell, q0, q1, c, fs, n0=4, dmax=24):
    """certified upper bound of sup_{q in [q0, q1]} Re(c f(z(q))) (branch and bound; pieces cover the arc)."""
    q0, q1 = F(q0), F(q1)
    tol = (c.abs_upper() * arb(2) ** -30).upper()
    work = []
    best = None
    for i in range(n0):
        a, b = q0 + (q1 - q0) * F(i, n0), q0 + (q1 - q0) * F(i + 1, n0)
        lo, hi, gm = g_bounds(ell, a, b, c, fs)
        best = amax_(gm.lower(), best)
        work.append((a, b, 0, hi))
    out = None
    while work:
        a, b, d, hi = work.pop()
        if hi <= best + tol or d >= dmax:
            out = amax_(hi, out)
            continue
        m = (a + b) / 2
        for x, y in ((a, m), (m, b)):
            lo2, hi2, gm2 = g_bounds(ell, x, y, c, fs)
            best = amax_(gm2.lower(), best)
            work.append((x, y, d + 1, hi2))
    return out


def arc_inf(ell, q0, q1, c, fs, **kw):
    return -arc_sup(ell, q0, q1, -c, fs, **kw)


# ------------------------------------------------------------------ t-sweep (mean-value form)
KC = {}                 # per-arc cache of coefficient-independent K values (cleared at the start of every arc)
KC_MAX = 3_000_000
KEYID = {}              # interned small integers for cache keys (hashing Fractions on every lookup is slow)


def keyid(key):
    if key is None:
        return None
    v = KEYID.get(key)
    if v is None:
        v = KEYID[key] = len(KEYID)
    return v


def kget(key, fn):
    if key is None:
        return fn()
    v = KC.get(key)
    if v is None:
        v = fn()
        if len(KC) < KC_MAX:
            KC[key] = v
    return v


class Geo:
    """geometry of an ellipse arc [q0, q1] (full enclosing box, sub-piece data), shared by the terms that use the arc."""
    def __init__(self, ell, q0, q1, key=None):
        self.ell = ell; self.q0 = F(q0); self.q1 = F(q1); self.key = keyid(key)
        self.box = ell.piece(q0, q1)[4]
        self.subs = {}

    def sub(self, n):
        if n not in self.subs:
            q0, q1 = self.q0, self.q1
            L = []
            for i in range(n):
                qm, h, zm, dzm, box, rho = self.ell.piece(q0 + (q1 - q0) * F(i, n), q0 + (q1 - q0) * F(i + 1, n))
                H = ar(h)
                L.append((zm, dzm, box.imag, H, H * H / 2))
            self.subs[n] = L
        return self.subs[n]


class PtTerm:
    """sup over the ball z of Re(c K_t(z))."""
    def __init__(self, c, z, key=None):
        self.c = c; self.z = z; self.dc = c * (-2 * PI * I1) * z; self.key = keyid(key)


class ArcTerm:
    """sup over z on the ellipse arc of geo of Re(c K_t(z)); at a fixed t, each sub-piece [qm - h, qm + h] contributes
    the second-order bound g(qm) + h |g'(qm)| + h^2/2 |c| (4 pi^2 t^2 vmax^2 + 2 pi |t| amax) sup_box |K_t|,
    g(q) = Re(c K_t(z(q)))."""
    def __init__(self, c, geo):
        self.c = c; self.geo = geo
        self.cd = c * (-2 * PI * I1)
        self.dc = self.cd * geo.box
        self.cabs = c.abs_upper()

    def upper_at(self, TM, n, d, k):
        """(upper bound of sup_{z on the arc} Re(c K_TM(z)), certified lower bound of it: the largest lower end of
        Re(c K_TM(z(qm))) over the sub-piece midpoints qm, which lie on the arc)"""
        g = self.geo; ell = g.ell
        best = None; low = None
        ta = TM.abs_upper()
        k2 = 4 * PI * PI * ta * ta * ell.vmax * ell.vmax + 2 * PI * ta * ell.amax
        c = self.c; cabs = self.cabs
        if g.key is not None:
            # coefficient-free data per (arc, n, piece, cell): K_TM(zm), w = -2 pi i z'(qm) TM K_TM(zm),
            # e = h^2/2 k2 sup_box |K_TM|; the bound below is the same as for unkeyed terms
            for i, (zm, dzm, bim, H, H2) in enumerate(g.sub(n)):
                key = (g.key, n, i, d, k)
                v = KC.get(key)
                if v is None:
                    Kz = Kt(TM, zm)
                    v = (Kz, (-2 * PI * I1) * dzm * TM * Kz, H2 * k2 * (2 * PI * (TM * bim).upper()).exp(), H)
                    if len(KC) < KC_MAX:
                        KC[key] = v
                Kz, w, e, H = v
                gv = (c * Kz).real
                b = gv + H * (c * w).real.abs_upper() + cabs * e
                best = amax_(b.upper(), best); low = amax_(gv.lower(), low)
            return best, low
        for i, (zm, dzm, bim, H, H2) in enumerate(g.sub(n)):
            # sup over the box of |K_t(z)| = exp(2 pi t Im z) <= exp(2 pi upper(t * Im(box)))
            Kz = Kt(TM, zm); Kb = (2 * PI * (TM * bim).upper()).exp()
            gv = (c * Kz).real
            g1 = (self.cd * dzm * TM * Kz).real
            b = gv + H * g1.abs_upper() + H2 * cabs * k2 * Kb
            best = amax_(b.upper(), best); low = amax_(gv.lower(), low)
        return best, low


TC = {}
def tcell(d, k):
    v = TC.get((d, k))
    if v is None:
        t0 = F(-1, 2) + F(k, 2 ** d); t1 = t0 + F(1, 2 ** d)
        v = (ar((t0 + t1) / 2), ar(t0).union(ar(t1)), ar(F(1, 2 ** (d + 1))))
        if len(TC) < 400000:
            TC[(d, k)] = v
    return v


def tsweep(terms, tauN, L, nsub):
    """certify tau_N * sup_t sum_i sup_{z in Z_i} Re(c_i K_t(z)) < L; returns (ok, U_max, cells, violated).
    violated = True: at a cell midpoint TM, tau_N * sum_i (certified lower bound of sup_{Z_i} Re(c_i K_TM)) > L, i.e.
    the inequality is false, so no sweep (any nsub, any depth) can certify it."""
    tau = ar(tauN)
    stack = [(0, 0)]
    umax = None; cells = 0
    while stack:
        d, k = stack.pop()
        cells += 1
        if cells > CELL_BUDGET:
            return False, None, cells, False
        TM, T, H = tcell(d, k)
        val = arb(0); der = arb(0); lo = arb(0)
        for tm in terms:
            if isinstance(tm, PtTerm):
                if tm.key is None:
                    KM = Kt(TM, tm.z); KT = Kt(T, tm.z)
                else:
                    KM, KT = kget((tm.key, d, k), lambda: (Kt(TM, tm.z), Kt(T, tm.z)))
                x = (tm.c * KM).real
                val += x.upper(); lo += x.lower()
                der += (tm.dc * KT).real
            else:
                u_, l_ = tm.upper_at(TM, nsub, d, k)
                val += u_; lo += l_
                g = tm.geo
                KT = Kt(T, g.box) if g.key is None else kget((g.key, "T", d, k), lambda: Kt(T, g.box))
                der += (tm.dc * KT).real
        U = val + H * der.abs_upper()
        if tau * U < L:
            umax = amax_(U.upper(), umax)
            continue
        if tau * lo > L:
            return False, None, cells, True
        if d >= TMAXDEPTH:
            return False, None, cells, False
        stack += [(d + 1, 2 * k), (d + 1, 2 * k + 1)]
    return True, umax, cells, False


def tsweep2(terms_fn, tauN, L, st):
    for n in NSUBS:
        ok, umax, cells, violated = tsweep(terms_fn(), tauN, L, n)
        st["cells"] = st.get("cells", 0) + cells
        if ok:
            return True, umax
        if violated:
            st["tsweep_violated"] = st.get("tsweep_violated", 0) + 1
            return False, None
    return False, None


def note(st, kind, L, umax, tauN):
    """bookkeeping only: tau-headroom L/U_max - tau_N of an accepted inequality."""
    if umax is None or not (umax > 0):
        return
    h = float((L / umax - ar(tauN)).mid())
    key = "hr_" + kind
    if key not in st or h < st[key]:
        st[key] = h


# ------------------------------------------------------------------ level-1 radius
def cos_range(x0, x1):
    """(lo, hi) arb bounds of cos(pi x) on [x0, x1] (exact rationals)."""
    c0 = arb.cos_pi_fmpq(fmpq(x0.numerator, x0.denominator)); c1 = arb.cos_pi_fmpq(fmpq(x1.numerator, x1.denominator))
    lo = c0.lower().min(c1.lower()); hi = c0.upper().max(c1.upper())
    n = -(-x0.numerator // x0.denominator)       # ceil(x0)
    while n <= x1:
        if n % 2 == 0:
            hi = arb(1)
        else:
            lo = arb(-1)
        n += 1
    return lo, hi


def sin_range(x0, x1):
    """(lo, hi) of sin(pi x) on [x0, x1]: maxima at x = 1/2 + 2k, minima at x = 3/2 + 2k."""
    s0 = arb.sin_pi_fmpq(fmpq(x0.numerator, x0.denominator)); s1 = arb.sin_pi_fmpq(fmpq(x1.numerator, x1.denominator))
    lo = s0.lower().min(s1.lower()); hi = s0.upper().max(s1.upper())
    y = x0 - F(1, 2); n = -(-y.numerator // y.denominator)     # x = 1/2 + n, n integer, x >= x0
    while F(1, 2) + n <= x1:
        if n % 2 == 0:
            hi = arb(1)
        else:
            lo = arb(-1)
        n += 1
    return lo, hi


def r1_both(T1, s0, s1, sc, zc, tauN):
    tau = ar(tauN)
    # disc version
    d = (T1.vmax * ar(max(s1 - sc, sc - s0))).upper()
    box = acb(zc.real + arb(0, d), zc.imag + arb(0, d))
    Y = (zc.imag.abs_upper() + d).upper()
    Smin = S0(box).abs_lower()
    if not (Smin > 0):
        raise ValueError("S not bounded away from 0 near the T1 arc (disc)")
    E = (PI * Y).exp()
    rd = (d * (tau * PI * E + tau * E / Smin * S1(box).abs_upper())).upper()
    # exact bounding box of the arc
    clo, chi = cos_range(2 * s0, 2 * s1); slo, shi = sin_range(2 * s0, 2 * s1)
    X = (T1.CR + T1.A * clo).union(T1.CR + T1.A * chi)
    Yi = (T1.CI + T1.B * slo).union(T1.CI + T1.B * shi)
    Zb = acb(X, Yi)
    db = (Zb - zc).abs_upper()
    Yb = Zb.imag.abs_upper().max(zc.imag.abs_upper())
    Smin_b = S0(Zb).abs_lower()
    if not (Smin_b > 0):
        raise ValueError("S not bounded away from 0 near the T1 arc (box)")
    Eb = (PI * Yb).exp()
    rb = (db * (tau * PI * Eb + tau * Eb / Smin_b * S1(Zb).abs_upper())).upper()
    return rd, rb


# ------------------------------------------------------------------ winding number
def winding(ell, at, n0=256, minw=F(1, 2 ** 30)):
    gcache = {}

    def Gq(q):
        v = gcache.get(q)
        if v is None:
            v = at.G0(ell.z(q)); gcache[q] = v
        return v
    total = arb(0)
    stack = [(F(k, n0), F(k + 1, n0)) for k in range(n0)]
    while stack:
        a, b = stack.pop()
        qm, h, zm, dzm, box, rho = ell.piece(a, b)
        gm = at.G0(zm)
        err = rho * at.G1(box).abs_upper()
        if gm.abs_lower() > 2 * err:
            total += (Gq(b) / Gq(a)).arg()
            continue
        if b - a < minw:
            return None
        m = (a + b) / 2
        stack += [(a, m), (m, b)]
    w = total / (2 * PI)
    n = int(round(float(w.mid())))
    if not (abs(w - n) < arb(1) / 4):
        return None
    return n


# ------------------------------------------------------------------ tubes, boxes
class Tube:
    def __init__(self, ell, q0, q1, base):
        self.ell = ell; self.q0 = F(q0); self.q1 = F(q1); self.base = base
        self.gfs = (base.G0, base.G1, base.G2)
        self.geo = Geo(ell, q0, q1, key=("geo", ell.cr, ell.ci, ell.a, ell.b, self.q0, self.q1))


def iv_bound(tb, vt, sign, eps):
    """sign -1 (W1): needs Re(conj vt G) <= 0 on the arc; returns sup Re(conj vt S) + |vt| eps.
       sign +1 (empty): needs >= 0; returns inf Re(conj vt S) - |vt| eps.  None if the sign condition is not certified."""
    c = conjb(vt)
    if not arc_sign(tb.ell, tb.q0, tb.q1, c, tb.gfs, sign):
        return None
    if sign < 0:
        return arc_sup(tb.ell, tb.q0, tb.q1, c, SFUN) + modb(vt) * ar(eps)
    return arc_inf(tb.ell, tb.q0, tb.q1, c, SFUN) - modb(vt) * ar(eps)


def box_max(y, Q):
    yr, yi = y; x0, x1, y0, y1 = Q
    return yr * (x1 if yr >= 0 else x0) + yi * (y1 if yi >= 0 else y0)


def box_min(y, Q):
    yr, yi = y; x0, x1, y0, y1 = Q
    return yr * (x0 if yr >= 0 else x1) + yi * (y0 if yi >= 0 else y1)


# ------------------------------------------------------------------ per-arc context and leaves
class Ctx:
    defer = None            # --deep pass 1: list collecting the hard tile-arc indices of the root W leaf defer_leaf
    defer_leaf = None


def r1_valid(ctx, tauN):
    key = F(tauN)
    v = ctx.r1c.get(key)
    if v is None:
        rd, rb = r1_both(ctx.T1, ctx.s0, ctx.s1, ctx.sc, ctx.zc, key)
        v = rd.min(rb)
        ctx.r1c[key] = v
        ctx.st["r1_disc_over_box_max"] = max(ctx.st.get("r1_disc_over_box_max", 0.0), float((rd / rb).mid()))
    return v


def get_tau(ctx, lf):
    tauN = F(lf.get("tau_rep", str(ctx.tau)))
    if not (ctx.tau <= tauN < 1):
        raise ValueError("tau_rep outside [tau, 1)")
    return tauN


def check_empty(ctx, Qs, tubes, lf):
    st = ctx.st
    tauN = get_tau(ctx, lf)
    v = cpl(lf["v"]); ys = [cpl(y) for y in lf["y"]]; vts = [cpl(x) for x in lf.get("vt", [])]
    if len(ys) != len(ctx.pcs) or len(vts) != len(tubes):
        return "empty: multiplier counts"
    X = (conjb(v) * ctx.Sc).real
    if not (X >= 0):
        return "empty: Re(conj v S(zc)) >= 0 not certified"
    L = X - modb(v) * r1_valid(ctx, tauN)
    for y, Q in zip(ys, Qs):
        L += ar(box_min(y, Q))
    for vt, tb in zip(vts, tubes):
        b = iv_bound(tb, vt, +1, ctx.eps)
        if b is None:
            return "empty: interval-tube sign condition not certified"
        L += b
    L = L.lower()
    if not (L > 0):
        return "empty: L > 0 fails"

    def terms():
        tl = [PtTerm(conjb(v), ctx.zc, ("zc",))]
        tl += [PtTerm(conjb(y), p, ("pc", j)) for j, (y, p) in enumerate(zip(ys, ctx.pcs))]
        tl += [ArcTerm(conjb(vt), tb.geo) for vt, tb in zip(vts, tubes)]
        return tl
    ok, umax = tsweep2(terms, tauN, L, st)
    if not ok:
        return "empty: t-sweep fails"
    note(st, "empty", L, umax, tauN)
    return None


def w1_arc(ctx, ell, q0, q1, u, B, tail, tauN, depth):
    st = ctx.st
    L = (arc_inf(ell, q0, q1, conjb(u), SFUN) - B).lower()
    if L > 0:
        ok, umax = tsweep2(lambda: [ArcTerm(conjb(u), Geo(ell, q0, q1))] + tail, tauN, L, st)
        if ok:
            note(st, "W1", L, umax, tauN)
            return True
    if depth >= W1_PDEPTH:
        return False
    st["w1_bisect"] = st.get("w1_bisect", 0) + 1
    m = (q0 + q1) / 2
    return w1_arc(ctx, ell, q0, m, u, B, tail, tauN, depth + 1) and w1_arc(ctx, ell, m, q1, u, B, tail, tauN, depth + 1)


def check_W(ctx, Qs, tubes, lf, nest):
    st = ctx.st
    tauN = get_tau(ctx, lf)
    if lf["tile"] not in ctx.tiles:
        return "W: unknown tile"
    ell = ctx.tiles[lf["tile"]]
    ts = [F(x) for x in lf["wrep_t"]]; ms = [F(x) for x in lf["wrep_m"]]
    if len(ts) != len(ms) or not ts:
        return "W: w_rep atoms"
    sigma = F(lf["sigma"])
    raw = lf.get("mus", [])
    if len(raw) != len(tubes):
        return "W: mus count"
    if any(m < 0 for m in ms) or sum(ms) > tauN or any(not (F(-1, 2) <= t <= F(1, 2)) for t in ts) or sigma < 1:
        return "W: w_rep not admissible"
    rep = Atoms(ts, ms)
    cv = (rep.what(ctx.zc) - ar(sigma) * ctx.Sc).abs_upper()
    r1v = r1_valid(ctx, tauN)
    r1N = r1v.max(cv)
    if cv > r1v:
        st["rep_above_r1valid"] = st.get("rep_above_r1valid", 0) + 1
    for p, Q in zip(ctx.pcs, Qs):
        x = rep.what(p)
        if not (x.real >= ar(Q[0]) and x.real <= ar(Q[1]) and x.imag >= ar(Q[2]) and x.imag <= ar(Q[3])):
            return "W: w_rep^(p_j) outside its box"
    for x, tb in zip(raw, tubes):
        if not (isinstance(x, list) and len(x) == 2):
            return "W: interval tube needs [q_r, mu_r]"
        qr, mu = F(x[0]), F(x[1])
        if not (tb.q0 <= qr <= tb.q1) or mu < 0:
            return "W: q_r outside the hard arc or mu_r < 0"
        zr = tb.ell.z(qr)
        if not ((rep.what(zr) - S0(zr) - ar(mu) * tb.base.G0(zr)).abs_upper() <= ar(ctx.eps)):
            return "W: w_rep violates an interval tube"
    n = winding(ell, rep)
    st.setdefault("wind", {})
    st["wind"][str(n)] = st["wind"].get(str(n), 0) + 1
    if n is None or n % 2 == 0:
        return f"W: winding {n} not odd"
    m = len(ctx.pcs); K = len(tubes)
    items = []
    for ix, a in enumerate(lf["tile_arcs"]):
        if isinstance(a, dict):
            if a.get("kind", "disc") != "iv":
                return "W: only interval ('iv') hard arcs are supported"
            q0, q1 = F(a["hard"][0]), F(a["hard"][1])
            items.append((q0, q1, "hard", a["child"], ix))
        else:
            if not isinstance(a, list) or len(a) != 6 + 2 * m + 2 * K:
                return "W: tile arc length"
            items.append((F(a[0]), F(a[1]), "w1", a, ix))
    items.sort(key=lambda x: x[0])
    if not items or items[0][0] != 0 or items[-1][1] != 1:
        return "W: tile arcs do not cover [0, 1]"
    for i in range(len(items)):
        if not items[i][0] < items[i][1]:
            return "W: empty tile arc"
        if i + 1 < len(items) and items[i][1] != items[i + 1][0]:
            return "W: tile arcs not contiguous"
    for q0, q1, kind, a, ix in items:
        if kind == "w1":
            st["W1"] = st.get("W1", 0) + 1
            u = cpl(a[2:4]); v = cpl(a[4:6])
            ys = [cpl(a[6 + 2 * j: 8 + 2 * j]) for j in range(m)]
            vts = [cpl(a[6 + 2 * m + 2 * k: 8 + 2 * m + 2 * k]) for k in range(K)]
            X = (conjb(v) * ctx.Sc).real
            if not (X <= 0):
                return f"W1 [{q0},{q1}]: Re(conj v S(zc)) <= 0 not certified"
            B = X + modb(v) * r1N
            for y, Q in zip(ys, Qs):
                B += ar(box_max(y, Q))
            for vt, tb in zip(vts, tubes):
                b = iv_bound(tb, vt, -1, ctx.eps)
                if b is None:
                    return f"W1 [{q0},{q1}]: interval-tube sign condition not certified"
                B += b
            B = B.upper()
            tail = [PtTerm(-conjb(v), ctx.zc, ("zc",))] + [PtTerm(-conjb(y), p, ("pc", j)) for j, (y, p) in enumerate(zip(ys, ctx.pcs))]
            tail += [ArcTerm(-conjb(vt), tb.geo) for vt, tb in zip(vts, tubes)]
            if not w1_arc(ctx, ell, q0, q1, u, B, tail, tauN, 0):
                return f"W1 fails on tile arc [{q0},{q1}] (tile {lf['tile']}, nest {nest})"
        else:
            st["hard"] = st.get("hard", 0) + 1
            if ctx.defer is not None and lf is ctx.defer_leaf:
                ctx.defer.append(ix)        # --deep: checked by check_child as a separate job (same tube, nest 1)
                continue
            err = check_node(ctx, a, Qs, tubes + [Tube(ell, q0, q1, rep)], nest + 1)
            if err:
                return f"hard [{q0},{q1}] -> {err}"
    return None


def check_node(ctx, node, Qs, tubes, nest):
    st = ctx.st
    if not isinstance(node, dict):
        return "node is not an object"
    if "ivsplit" in node:
        k = node["ivsplit"]
        kids = node.get("kids")
        if not (isinstance(k, int) and not isinstance(k, bool) and 0 <= k < len(tubes)):
            return "bad ivsplit node (tube index)"
        if not (isinstance(kids, list) and len(kids) == 2) or "at" not in node or "split" in node:
            return "bad ivsplit node (kids or split point)"
        try:
            qm = F(node["at"])
        except (ValueError, TypeError, ZeroDivisionError, OverflowError):
            return "bad ivsplit node (split point)"
        tb = tubes[k]
        if not (tb.q0 < qm < tb.q1):
            return "bad ivsplit node (split point not interior to the tube arc)"
        st["ivsplit"] = st.get("ivsplit", 0) + 1
        for (a, b), kid in zip(((tb.q0, qm), (qm, tb.q1)), kids):
            T2 = list(tubes); T2[k] = Tube(tb.ell, a, b, tb.base)
            err = check_node(ctx, kid, Qs, T2, nest)
            if err:
                return f"ivsplit tube {k} [{a},{b}] -> {err}"
        return None
    if "split" in node:
        j = node["split"]
        if not (isinstance(j, int) and 0 <= j < len(Qs)) or len(node.get("kids", [])) != 4:
            return "bad split node"
        x0, x1, y0, y1 = Qs[j]; mx = (x0 + x1) / 2; my = (y0 + y1) / 2
        for kid, q in zip(node["kids"], [(x0, mx, y0, my), (mx, x1, y0, my), (x0, mx, my, y1), (mx, x1, my, y1)]):
            Q2 = list(Qs); Q2[j] = q
            err = check_node(ctx, kid, Q2, tubes, nest)
            if err:
                return err
        return None
    stored = [tuple(F(b) for b in bx) for bx in node.get("boxes", [])]
    if stored != list(Qs):
        st["box_mismatch"] = st.get("box_mismatch", 0) + 1     # the boxes used are the tree-position boxes
    st["leaves"] = st.get("leaves", 0) + 1
    st["maxnest"] = max(st.get("maxnest", 0), nest)
    t = node.get("type")
    if t == "empty":
        st["empty"] = st.get("empty", 0) + 1
        return check_empty(ctx, Qs, tubes, node)
    if t == "W":
        st["W"] = st.get("W", 0) + 1
        return check_W(ctx, Qs, tubes, node, nest)
    return "unknown leaf type"


def check_E(G, s0, s1, u, st, depth=0):
    T1 = G["T1"]
    c = conjb(u)
    L = arc_inf(T1, s0, s1, c, SFUN).lower()
    if L > 0:
        ok, umax = tsweep2(lambda: [ArcTerm(c, Geo(T1, s0, s1))], G["tau"], L, st)
        if ok:
            note(st, "E", L, umax, G["tau"])
            return True
    if depth >= E_DEPTH:
        return False
    m = (s0 + s1) / 2
    return check_E(G, s0, m, u, st, depth + 1) and check_E(G, m, s1, u, st, depth + 1)


def check_arc(arc, G, defer=None):
    KC.clear()
    st = {}
    t = arc.get("type")
    s0, s1 = F(arc["s0"]), F(arc["s1"])
    if t == "E":
        ok = check_E(G, s0, s1, cpl(arc["u"]), st)
        return (None if ok else "E fails"), st
    if t not in ("N", "H3", "H"):
        return "unknown arc type", st
    r = arc_setup(arc, G, st)
    if isinstance(r, str):
        return r, st
    ctx, tree, Qs = r
    if defer is not None:
        ctx.defer = defer; ctx.defer_leaf = tree     # only a root W leaf (tree itself) defers its hard subtrees
    try:
        err = check_node(ctx, tree, Qs, [], 0)
    except (ValueError, KeyError, TypeError, IndexError, ZeroDivisionError) as e:
        err = f"malformed or failing data: {type(e).__name__}: {e}"
    return err, st


def check_child(head, entry, G):
    """--deep pass 2: the subtree below one hard tile arc (entry) of the ROOT W leaf of a rooted arc, checked as check_W
    checks it: same arc context and root boxes, tube list [(root tile, [q0, q1], root w_rep)], nesting level 1.
    head = the arc without its heavy data (for N/H3 the root leaf without tile_arcs; for H tile_arcs = [])."""
    KC.clear()
    st = {}
    if head.get("type") not in ("N", "H3", "H"):
        return "deep: unknown arc type", st
    r = arc_setup(head, G, st)
    if isinstance(r, str):
        return r, st
    ctx, lf, Qs = r
    try:
        if not (isinstance(lf, dict) and lf.get("type") == "W" and "split" not in lf and "ivsplit" not in lf):
            return "deep: root is not a W leaf", st
        if lf["tile"] not in ctx.tiles:
            return "W: unknown tile", st
        ell = ctx.tiles[lf["tile"]]
        rep = Atoms([F(x) for x in lf["wrep_t"]], [F(x) for x in lf["wrep_m"]])
        if not (isinstance(entry, dict) and entry.get("kind", "disc") == "iv"):
            return "deep: not an interval hard arc", st
        q0, q1 = F(entry["hard"][0]), F(entry["hard"][1])
        err = check_node(ctx, entry["child"], Qs, [Tube(ell, q0, q1, rep)], 1)
        if err:
            err = f"hard [{q0},{q1}] -> {err}"
    except (ValueError, KeyError, TypeError, IndexError, ZeroDivisionError) as e:
        err = f"malformed or failing data: {type(e).__name__}: {e}"
    return err, st


def arc_setup(arc, G, st):
    """context (ctx, tree, Qs) of a rooted arc, or an error string"""
    t = arc.get("type")
    s0, s1 = F(arc["s0"]), F(arc["s1"])
    sc = F(arc["sc"])
    if not (s0 <= sc <= s1):
        return "sc outside the arc"
    ctx = Ctx()
    ctx.st = st; ctx.tau = G["tau"]; ctx.eps = G["eps"]; ctx.T1 = G["T1"]; ctx.tiles = G["tiles"]
    ctx.s0, ctx.s1, ctx.sc = s0, s1, sc
    ctx.zc = ctx.T1.z(sc); ctx.Sc = S0(ctx.zc); ctx.r1c = {}
    if t == "H":
        ctx.pcs = []
        tree = {"boxes": [], "type": "W", "tile": arc["tile"], "tile_arcs": arc["tile_arcs"], "wrep_t": arc["wrep_t"],
                "wrep_m": arc["wrep_m"], "sigma": arc["sigma"]}
        Qs = []
    else:
        pts = [cpl(p) for p in arc.get("pcs", [])]
        Rs = [F(R) for R in arc.get("Rs", [])]
        if len(Rs) != len(pts):
            return "pcs/Rs mismatch"
        ctx.pcs = [acb(ar(a), ar(b)) for a, b in pts]
        for (a, b), R in zip(pts, Rs):
            if not (ar(R) >= ar(ctx.tau) * (PI * abs(ar(b))).exp()):
                return "root box too small"
        Qs = [(-R, R, -R, R) for R in Rs]
        tree = arc["tree"]
    return ctx, tree, Qs


# ------------------------------------------------------------------ driver
GL = {}
def init(g):
    GL.clear()
    GL["tau"] = F(g["tau"]); GL["eps"] = F(g["eps"])
    GL["T1"] = Ell(*g["T1"])
    GL["tiles"] = {k: Ell(*v) for k, v in g["tiles"].items()}


def work(item):
    i, arc = item
    t0 = time.time()
    try:
        err, st = check_arc(arc, GL)
    except RecursionError:
        err, st = "recursion limit", {}
    return {"i": i, "s0": str(arc.get("s0")), "type": arc.get("type"), "ok": err is None, "msg": err or "", "st": st,
            "sec": round(time.time() - t0, 3)}


def work_deep1(item):
    """--deep pass 1: the arc without the subtrees below its root W leaf's hard tile arcs (their indices are returned)"""
    i, arc = item
    t0 = time.time(); defer = []
    try:
        err, st = check_arc(arc, GL, defer)
    except RecursionError:
        err, st = "recursion limit", {}
    return {"i": i, "s0": str(arc.get("s0")), "type": arc.get("type"), "ok": err is None, "msg": err or "", "st": st,
            "sec": round(time.time() - t0, 3), "jobs": defer if err is None else []}


def work_deep2(item):
    """--deep pass 2: one deferred subtree"""
    i, ix, head, entry = item
    t0 = time.time()
    try:
        err, st = check_child(head, entry, GL)
    except RecursionError:
        err, st = "recursion limit", {}
    return {"i": i, "ix": ix, "ok": err is None, "msg": err or "", "st": st, "sec": round(time.time() - t0, 3)}


def merge_st(tot, st):
    for k, v in st.items():
        if k == "wind":
            w = tot.setdefault("wind", {})
            for kk, vv in v.items():
                w[kk] = w.get(kk, 0) + vv
        elif k.startswith("hr_"):
            tot[k] = min(tot.get(k, v), v)
        elif k in ("maxnest", "r1_disc_over_box_max"):
            tot[k] = max(tot.get(k, v), v)
        else:
            tot[k] = tot.get(k, 0) + v


def root_tile_arcs(arc):
    """the tile_arcs list of the root W leaf of a rooted arc (None if the root is not a W leaf)"""
    t = arc.get("type")
    if t == "H":
        tas = arc.get("tile_arcs")
    elif t in ("N", "H3"):
        tree = arc.get("tree")
        if not (isinstance(tree, dict) and tree.get("type") == "W" and "split" not in tree and "ivsplit" not in tree):
            return None
        tas = tree.get("tile_arcs")
    else:
        return None
    return tas if isinstance(tas, list) else None


def deep_pass1_copy(arc):
    """pass-1 copy: the children of the root W leaf's hard tile arcs replaced by None (pass 1 does not read them)"""
    tas = root_tile_arcs(arc)
    if tas is None:
        return arc
    tas = [dict(a, child=None) if isinstance(a, dict) else a for a in tas]
    if arc.get("type") == "H":
        return dict(arc, tile_arcs=tas)
    return dict(arc, tree=dict(arc["tree"], tile_arcs=tas))


def deep_head(arc):
    """pass-2 head: the arc without the root leaf's tile_arcs"""
    if arc.get("type") == "H":
        return dict(arc, tile_arcs=[])
    return dict(arc, tree={k: v for k, v in arc["tree"].items() if k != "tile_arcs"})


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    sel = None
    for a in sys.argv[1:]:
        if a.startswith("--arcs="):
            sel = [int(x) for x in a[7:].split(",") if x]
    deep = "--deep" in sys.argv[1:]
    path, nproc, out = args[0], int(args[1]), args[2]
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt") as fh:
        C = json.load(fh)
    if C.get("variant") != "Cp":
        sys.exit("FAIL: variant")
    tau = F(C["tau"])
    if not (0 < tau < 1):
        sys.exit("FAIL: tau")
    c, a, b = (F(x) for x in C["T1"])
    if not (a > 0 and b > 0):
        sys.exit("FAIL: T1 axes")
    lo, hi = c - a, c + a
    zeros = [n for n in range(int(lo) - 2, int(hi) + 3) if n != 0 and lo < n < hi]
    if len(zeros) != 1:
        sys.exit(f"FAIL: T1 encloses zeros {zeros}")
    if (lo.denominator == 1 and lo != 0) or (hi.denominator == 1 and hi != 0):
        sys.exit("FAIL: S vanishes on T1")
    eps = F(C.get("iv_eps", "1/1000000000"))
    if not (0 <= eps <= F(1, 1000)):
        sys.exit("FAIL: eps")
    tiles = {k: [str(F(x)) for x in v] for k, v in C["tiles"].items()}
    for k, v in tiles.items():
        if len(v) != 4 or not (F(v[2]) > 0 and F(v[3]) > 0):
            sys.exit(f"FAIL: tile {k}")
    arcs = C["arcs"]
    if "--subset" in sys.argv[1:]:
        sel = list(range(len(arcs)))
    order = sorted(range(len(arcs)), key=lambda i: F(arcs[i]["s0"]))
    for i in order:
        if not F(arcs[i]["s0"]) < F(arcs[i]["s1"]):
            sys.exit("FAIL: empty T1 arc")
    if sel is None:
        if F(arcs[order[0]]["s0"]) != 0 or F(arcs[order[-1]]["s1"]) != 1:
            sys.exit("FAIL: arcs do not cover [0, 1]")
        for x, y in zip(order, order[1:]):
            if F(arcs[x]["s1"]) != F(arcs[y]["s0"]):
                sys.exit("FAIL: arcs not contiguous")
    g = {"tau": str(tau), "eps": str(eps), "T1": [str(c), "0", str(a), str(b)], "tiles": tiles}
    print(f"global checks OK: tau = {tau}, T1 = {C['T1']} (zero {zeros[0]} inside), {len(arcs)} arcs, eps = {eps}, "
          f"{len(tiles)} tiles", flush=True)
    items = [(i, arcs[i]) for i in (sel if sel is not None else order)]
    del C, arcs
    import multiprocessing as mp
    ctxm = mp.get_context("spawn")
    t0 = time.time(); nbad = 0; tot = {}; done = 0
    if deep:
        res = {}
        with ctxm.Pool(nproc, initializer=init, initargs=(g,)) as pool:
            for r in pool.imap_unordered(work_deep1, [(i, deep_pass1_copy(x)) for i, x in items], chunksize=1):
                res[r["i"]] = r
            full = dict(items)
            jobs = []
            for i, r in res.items():
                if r["jobs"]:
                    arc = full[i]; tas = root_tile_arcs(arc); head = deep_head(arc)
                    assert tas is not None and len(set(r["jobs"])) == len(r["jobs"]), "deep: job list"
                    for ix in r["jobs"]:
                        jobs.append((i, ix, head, tas[ix]))
                r["jobs"] = len(r["jobs"])
            jobs.sort(key=lambda j: -len(json.dumps(j[3])))     # largest subtrees first (scheduling only)
            print(f"deep mode: pass 1 done ({len(items)} arcs, {sum(1 for r in res.values() if not r['ok'])} failed), "
                  f"{len(jobs)} subtree jobs [{time.time() - t0:.0f}s]", flush=True)
            with open(out + ".jobs", "w") as fj:
                for r in pool.imap_unordered(work_deep2, jobs, chunksize=1):
                    fj.write(json.dumps(r) + "\n"); fj.flush()
                    a_ = res[r["i"]]
                    if not r["ok"] and a_["ok"]:
                        a_["ok"] = False; a_["msg"] = r["msg"]
                    merge_st(a_["st"], r["st"]); a_["sec"] = round(a_["sec"] + r["sec"], 3)
                    done += 1
                    if done % max(1, len(jobs) // 20) == 0:
                        print(f"  [{time.time() - t0:7.0f}s] {done}/{len(jobs)} subtree jobs", flush=True)
        with open(out, "w") as fo:
            for i, _ in items:
                r = res[i]
                fo.write(json.dumps(r) + "\n")
                if not r["ok"]:
                    nbad += 1
                    print(f"  arc {r['i']} (s0 {r['s0']}, {r['type']}) FAILED: {r['msg']}", flush=True)
                merge_st(tot, r["st"])
    else:
        with ctxm.Pool(nproc, initializer=init, initargs=(g,)) as pool, open(out, "w") as fo:
            for r in pool.imap_unordered(work, items, chunksize=1):
                fo.write(json.dumps(r) + "\n"); fo.flush()
                done += 1
                if not r["ok"]:
                    nbad += 1
                    print(f"  arc {r['i']} (s0 {r['s0']}, {r['type']}) FAILED: {r['msg']}", flush=True)
                merge_st(tot, r["st"])
                if done % max(1, len(items) // 20) == 0:
                    print(f"  [{time.time() - t0:7.0f}s] {done}/{len(items)} arcs, {nbad} failed", flush=True)
    nE = sum(1 for _, x in items if x.get("type") == "E")
    print(f"checked {len(items)} arcs ({nE} E, {len(items) - nE} rooted); totals {json.dumps(tot, sort_keys=True)}; "
          f"wall {time.time() - t0:.0f}s", flush=True)
    if nbad:
        print(f"FAILED: {nbad} of {len(items)} arcs")
        sys.exit(1)
    if sel is not None:
        print(f"SUBSET OK: {len(items)} arcs pass (no coverage claim)")
        return
    print(f"OK (FULL): all conditions verified; tau = {tau}; => ess sup f*f > {1 / (1 - tau)} (int f)^2 = "
          f"{float(1 / (1 - tau)):.10f} (int f)^2")


if __name__ == "__main__":
    sys.setrecursionlimit(20000)
    main()
