"""Milestone M4 exporter: certificate data for the kernel checker AutocorrK (Core.lean).

* `kp_constants(n)`: the KP record (descriptor table T with key fields, sym patterns, internal-block table, and the
  product-column table canonTab of the square cuts: entry canon(d, e) in the 16-bit slot d * 128 + e).
* `Flattener`: global DFS over the job logs (S records expanded), exact regions (verify.Spec), per split the
  numbers of propagation sweeps with changes (k0, k1), per leaf the KC duals (rounded to 2^-64, rescaled
  window rows) re-checked exactly with kc_ref.  Records are encoded as in AutocorrK.runK.
* `pk_box`, `pk_stack`: packed boxes / stacks for segment interfaces.
"""
import sys, os, json, gzip, glob
from fractions import Fraction as Fr

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checker_path
checker_path.add_checker_path()
import verify
import kc_ref

KIND = {"win": 0, "P": 1, "G": 2, "tree": 3, "ZA": 4, "rlt": 5, "sym": 6, "mc": 7}
SB = 30


def descriptor(ks, key):
    """80-bit descriptor: kind | f1..f4 (12 each) | flag | k1, k2, k3 (7 each)."""
    n = ks.n
    kind = key[0]
    f = [0, 0, 0, 0]; flag = 0; kk = [0, 0, 0]
    if kind == "win":
        c1, c2 = key[1], key[2]
        f = [ks.oG + c2, ks.oG + c1 - 1 if c1 > 0 else 0, c2 - c1 + 2, 0]; flag = int(c1 > 0); kk = [c1, c2, 0]
    elif kind == "P":
        c = key[1]; f = [ks.oP + c, c, 0, 0]; kk = [c, 0, 0]
    elif kind == "G":
        c = key[1]; f = [ks.oG + c, ks.oP + c, ks.oG + c - 1 if c > 0 else 0, 0]; flag = int(c > 0); kk = [c, 0, 0]
    elif kind == "tree":
        b = key[1]; f = [b, ks.c1[b], ks.c2[b], 0]; kk = [b, 0, 0]
    elif kind == "ZA":
        d, e, s = key[1], key[2], key[3]
        o = e if s == d else d
        s1, s2 = ks.c1[s], ks.c2[s]
        if d == e:
            f = [ks.canon(d, e), ks.canon(s1, s1), ks.canon(s2, s2), ks.canon(s1, s2)]; flag = 1
        else:
            f = [ks.canon(d, e), ks.canon(s1, o), ks.canon(s2, o), 0]
        kk = [d, e, s]
    elif kind == "rlt":
        i = key[1]; f = [i, ks.leaf_of[i], 0, 0]; kk = [i, 0, 0]
    elif kind == "sym":
        pass
    elif kind == "mc":
        d, e, q = key[1], key[2], key[3]
        f = [ks.canon(d, e), d, e, q]; flag = int(d == e); kk = [d, e, q]
    x = KIND[kind]
    for i in range(4):
        assert 0 <= f[i] < 8192
        x |= f[i] << (3 + 13 * i)
    x |= flag << 55
    for i in range(3):
        assert 0 <= kk[i] < 128
        x |= kk[i] << (56 + 7 * i)
    return x


def kp_constants(n, rowkeys):
    ks = kc_ref.KSpec(n)
    T = 0
    for i, k in enumerate(rowkeys):
        T |= descriptor(ks, tuple(k)) << (80 * i)
    symP = symN = 0
    for i in range(n):
        a = (2 * i - (n - 1)) << SB
        if a > 0:
            symP |= a << (136 * ks.leaf_of[i])
        elif a < 0:
            symN |= (-a) << (136 * ks.leaf_of[i])
    ints = [b for b in range(ks.nB) if ks.c1[b] >= 0]
    intTab = 0
    for j, b in enumerate(ints):
        intTab |= (b | (ks.c1[b] << 7) | (ks.c2[b] << 14)) << (21 * j)
    canonTab = 0
    for d in range(ks.nB):
        for e in range(ks.nB):
            c = ks.canon(d, e)
            assert 0 <= c < (1 << 16)
            canonTab |= c << (16 * (128 * d + e))
    return dict(n=n, nB=ks.nB, oZ=ks.oZ, oP=ks.oP, oG=ks.oG, NC1=ks.oT, NR=len(rowkeys), T=T,
                symP=symP, symN=symN, intTab=intTab, nInt=len(ints), canonTab=canonTab), ks


def lean_kp(name, kp):
    return (f"noncomputable def {name} : AutocorrK.KP := ⟨{kp['n']}, {kp['nB']}, {kp['oZ']}, {kp['oP']}, "
            f"{kp['oG']}, {kp['NC1']}, {kp['NR']}, {kp['T']}, {kp['symP']}, {kp['symN']}, {kp['intTab']}, "
            f"{kp['nInt']}, {kp['canonTab']}⟩")


def propagate_count(spec, L, U):
    """verify.Spec.propagate with the number of sweeps that changed something."""
    L = list(L); U = list(U); tree = spec.tree
    L[0] = max(L[0], Fr(1)); U[0] = min(U[0], Fr(1))
    k = 0
    for _ in range(64):
        changed = False
        for b, (lo, hi, par, c1, c2) in enumerate(tree):
            if c1 < 0:
                continue
            nl = max(L[b], L[c1] + L[c2]); nu = min(U[b], U[c1] + U[c2])
            l1 = max(L[c1], L[b] - U[c2]); u1 = min(U[c1], U[b] - L[c2])
            l2 = max(L[c2], L[b] - U[c1]); u2 = min(U[c2], U[b] - L[c1])
            new = (nl, nu, l1, u1, l2, u2)
            if new != (L[b], U[b], L[c1], U[c1], L[c2], U[c2]):
                changed = True
                L[b], U[b], L[c1], U[c1], L[c2], U[c2] = new
        if not changed:
            break
        k += 1
    else:
        raise RuntimeError("no convergence")
    if any(L[b] > U[b] for b in range(spec.nB)):
        return None, k
    return (L, U), k


def child_count(spec, reg, b, s, side):
    L, U = list(reg[0]), list(reg[1])
    if side == 0:
        U[b] = s
    else:
        L[b] = s
    return propagate_count(spec, L, U)


def pk_box(reg):
    lp = sum(int(x * (1 << SB)) << (32 * b) for b, x in enumerate(reg[0]))
    up = sum(int(x * (1 << SB)) << (32 * b) for b, x in enumerate(reg[1]))
    return lp, up


def enc_split(b, s, k0, k1):
    sv = s * (1 << SB)
    assert sv.denominator == 1 and 0 <= sv.numerator < (1 << 31) and b < 128 and k0 < 16 and k1 < 16
    return (0 | (b << 1) | (sv.numerator << 8) | (k0 << 39) | (k1 << 43)), 47


def enc_leaf(rindex, duals):
    cnt = len(duals)
    assert cnt < 16384
    x = 1 | (cnt << 1)
    for j, (key, Y) in enumerate(duals):
        assert abs(Y) < (1 << 72)
        x |= (rindex[key] | ((1 if Y < 0 else 0) << 14) | (abs(Y) << 15)) << (15 + 87 * j)
    return x, 15 + 87 * cnt


class Packer:
    """Little-endian bit packer."""
    def __init__(self):
        self.parts = []
        self.nbits = 0

    def add(self, v, w):
        self.parts.append((v, self.nbits))
        self.nbits += w

    def value(self):
        x = 0
        for v, off in self.parts:
            x |= v << off
        return x
