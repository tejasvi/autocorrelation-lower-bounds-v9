"""Reference implementation (exact integers) of the kernel checker's leaf bound (milestone M4).

Differences from verify.leaf_bound, all of which keep the bound valid:
  * duals are rounded to the grid 2^-D (D = 64);
  * the window row is rescaled: winK(c1,c2): G_c2 - G_{c1-1} - (k/2n) t <= 0 with k = c2-c1+2, whose dual is
    y' = y * 2n/k (rounded);
  * everything is computed in integers:
      R_c (c != t)  = 2^(D+30) * r_c       (reduced cost; all coefficients lie in 2^-30 Z)
      T             = 2n * 2^D * r_t
      A             = 2^(D+60) * rowpart
      LBs           = 2n*A + 2n*sum_m min(R l, R u) + 2n*2^30*sum_[0,1] min(0, R) + 2^60*min(0, 3T)
                    = 2n * 2^(D+60) * LB,
    accepted iff b*LBs >= a*2n*2^(D+60) for lam = a/b.
Square cuts (format 2, verify_cmp.Spec.sq_row): key ("sq", v0, d, v1, e, v2) for the row
    v1^2 [m_d m_d] + 2 v1 v2 [m_d m_e] + v2^2 [m_e m_e] + 2 v0 v1 m_d + 2 v0 v2 m_e >= -v0^2
(a one-term key is written with e = d, v2 = 0); its KC dual is M = floor(y * 2^94) >= 0 (any y >= 0 is admissible), so
    R_c += -M * a_c,   A += -M * v0^2 * 2^30.
"""
import sys, os
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checker_path
checker_path.add_checker_path()
import verify

D = 64
SB = 30


class KSpec:
    def __init__(self, n):
        self.n = n
        sp = verify.Spec(n)
        self.sp = sp
        self.nB = sp.nB
        self.tree = sp.tree
        self.leaf = sp.leaf
        self.lo = [t[0] for t in sp.tree]
        self.c1 = [t[3] for t in sp.tree]
        self.c2 = [t[4] for t in sp.tree]
        self.leaf_of = [sp.leaf_of_bin[i] for i in range(n)]
        nB = self.nB
        self.oZ = nB
        self.oZA = nB + n * n
        self.oP = self.oZA + nB * nB
        self.oG = self.oP + 2 * n - 1
        self.oT = self.oG + 2 * n - 1
        self.NC = self.oT + 1

    def zidx(self, i, j):
        return self.oZ + min(i, j) * self.n + max(i, j)

    def canon(self, d, e):
        if self.leaf[d] and self.leaf[e]:
            return self.zidx(self.lo[d], self.lo[e])
        return self.oZA + min(d, e) * self.nB + max(d, e)


def round_dual(y):
    """Round y (Fraction) to the nearest multiple of 2^-D; returns the integer numerator."""
    v = y * (1 << D)
    return int(round(v))


def kc_duals(ks, rowkeys, idx, vals):
    """Convert verify.py duals to KC duals: list of (key, Y) with the window rows rescaled."""
    out = []
    n = ks.n
    for k, v in zip(idx, vals):
        key = tuple(rowkeys[k])
        y = Fr(v)
        if y == 0:
            continue
        if key[0] == "win":
            c1, c2 = key[1], key[2]
            y = y * Fr(2 * n, c2 - c1 + 2)
        Y = round_dual(y)
        if Y != 0:
            out.append((key, Y))
    return out


CUT_M = (1 << 64) - 1     # largest M of one cut record (AutocorrK: 64-bit field)
CUT_V = 1 << 21           # |v| < 2^21 (AutocorrK: 21-bit magnitudes)


def kc_cut_duals(extras):
    """Square-cut entries [(key, y)] (verify_cmp format, y Fraction) -> KC cut duals [(("sq", v0, d, v1, e, v2), M)].
    Duals y <= 0 are dropped (a cut row is ">=", so a negative multiplier is inadmissible and contributes nothing).
    A multiplier above CUT_M is split into several records of the same cut (the bound is linear in them)."""
    out = []
    for key, y in extras:
        y = Fr(y)
        if y <= 0:
            continue
        if not (isinstance(key, (list, tuple)) and len(key) == 3 and key[0] == "sq"):
            raise ValueError(f"bad square-cut key {key!r}")
        v0 = int(key[1])
        terms = [(int(b), int(v)) for b, v in key[2] if int(v) != 0]
        if len(terms) == 1:
            (d, v1), = terms; e, v2 = d, 0
        elif len(terms) == 2:
            (d, v1), (e, v2) = terms
        else:
            raise ValueError(f"square cut with {len(terms)} nonzero terms is not supported by the kernel checker")
        if not all(abs(v) < CUT_V for v in (v0, v1, v2)):
            raise ValueError(f"square-cut coefficient too large for the kernel checker: {key!r}")
        M = (y * (1 << (D + SB))).__floor__()
        while M > 0:
            c = min(M, CUT_M)
            out.append((("sq", v0, d, v1, e, v2), c))
            M -= c
    return out


def kc_bound(ks, L, U, duals):
    """L, U: lists of Fractions (multiples of 2^-30). Returns LBs (integer, = 2n 2^(D+60) LB)."""
    n = ks.n
    l = [int(x * (1 << SB)) for x in L]
    u = [int(x * (1 << SB)) for x in U]
    R = {}
    T = 2 * n << D
    A = 0
    S30 = 1 << SB

    def add(c, v):
        R[c] = R.get(c, 0) + v

    for key, Y in duals:
        kind = key[0]
        if kind == "win":
            if Y > 0:
                continue                  # lo = none
            c1, c2 = key[1], key[2]
            k = c2 - c1 + 2
            add(ks.oG + c2, -Y * S30)
            if c1 > 0:
                add(ks.oG + c1 - 1, Y * S30)
            T += Y * k
        elif kind == "P":
            c = key[1]
            add(ks.oP + c, -Y * S30)
            for i in range(n):
                if i <= c and c - i < n:
                    add(ks.zidx(i, c - i), Y * S30)
        elif kind == "G":
            c = key[1]
            add(ks.oG + c, -Y * S30)
            add(ks.oP + c, Y * S30)
            if c > 0:
                add(ks.oG + c - 1, Y * S30)
        elif kind == "tree":
            b = key[1]
            add(b, -Y * S30); add(ks.c1[b], Y * S30); add(ks.c2[b], Y * S30)
        elif kind == "ZA":
            d, e, s = key[1], key[2], key[3]
            o = e if s == d else d
            s1, s2 = ks.c1[s], ks.c2[s]
            add(ks.canon(d, e), -Y * S30)
            if d == e:
                add(ks.canon(s1, s1), Y * S30); add(ks.canon(s1, s2), 2 * Y * S30); add(ks.canon(s2, s2), Y * S30)
            else:
                add(ks.canon(s1, o), Y * S30); add(ks.canon(s2, o), Y * S30)
        elif kind == "rlt":
            i = key[1]
            for j in range(n):
                add(ks.zidx(i, j), -Y * S30)
            add(ks.leaf_of[i], Y * S30)
        elif kind == "sym":
            if Y > 0:
                continue
            for i in range(n):
                add(ks.leaf_of[i], -Y * (2 * i - (n - 1)) * S30)
        elif kind == "sq":
            assert Y > 0
            v0, d, v1, e, v2 = key[1], key[2], key[3], key[4], key[5]
            for c, a in ((ks.canon(d, d), v1 * v1), (ks.canon(e, e), v2 * v2), (ks.canon(d, e), 2 * v1 * v2),
                         (d, 2 * v0 * v1), (e, 2 * v0 * v2)):
                add(c, -Y * a)
            A -= Y * v0 * v0 * S30
        elif kind == "mc":
            if Y > 0:
                continue
            d, e, q = key[1], key[2], key[3]
            z = ks.canon(d, e)
            ld, ud, le, ue = l[d], u[d], l[e], u[e]
            if d == e:
                if q == 0:
                    cz, cd, rhs = -1, 2 * ld, ld * ld
                elif q == 1:
                    cz, cd, rhs = -1, 2 * ud, ud * ud
                else:
                    cz, cd, rhs = 1, -(ld + ud), -ld * ud
                add(z, -Y * cz * S30); add(d, -Y * cd)
            else:
                if q == 0:
                    cz, cd, ce, rhs = -1, le, ld, ld * le
                elif q == 1:
                    cz, cd, ce, rhs = -1, ue, ud, ud * ue
                elif q == 2:
                    cz, cd, ce, rhs = 1, -ue, -ld, -ld * ue
                else:
                    cz, cd, ce, rhs = 1, -le, -ud, -ud * le
                add(z, -Y * cz * S30); add(d, -Y * cd); add(e, -Y * ce)
            A += Y * rhs
        else:
            raise ValueError(kind)
    tot_m = 0
    tot_01 = 0
    for c, v in R.items():
        if v == 0:
            continue
        if c < ks.nB:
            tot_m += min(v * l[c], v * u[c])
        else:
            assert c != ks.oT
            tot_01 += min(0, v)
    LBs = 2 * n * A + 2 * n * tot_m + 2 * n * (tot_01 << SB) + (min(0, 3 * T) << 60)
    return LBs


def kc_accept(ks, lam, L, U, duals):
    LBs = kc_bound(ks, L, U, duals)
    return lam.denominator * LBs >= lam.numerator * 2 * ks.n * (1 << (D + 60)), Fr(LBs, 2 * ks.n * (1 << (D + 60)))
