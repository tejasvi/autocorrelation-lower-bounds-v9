#!/usr/bin/env python3
"""Export a three-level certificate (GGSTW Problem 6.4, one-sided, format of check_three_level_m.py) to Lean data for
the checker C64Core.Check.

Nothing in the output is trusted by the proofs: the Lean checker re-derives every condition.  The exporter only
re-encodes the certificate:
  * s (arcs of T1) as integers over 2^ES, q (tile arcs) as integers over 2^EQ;
  * the multipliers (u, v, y_1, ..., y_m) of a tile arc, (v, y) of an exclusion leaf and u of an E arc are scaled by
    the least common multiple of their denominators (the conditions are positively homogeneous in them);
  * a leaf is one natural number: length-prefixed fields read from the low bits upward (rdNat: 8-bit length;
    rdInt: sign bit + rdNat; rdQ: rdInt numerator + rdNat denominator).
Witness leaf: tile index, tau_rep, sigma, K, K atoms (t, m), N, N tile arcs (q1, u, v, y_1..y_m).
Exclusion leaf: v, y_1..y_m.

Usage:
  gen_lean_data.py CERT.json[.gz] OUTDIR --test K       one Lean file with K sampled arcs and #eval timings
  gen_lean_data.py CERT.json[.gz] OUTDIR --modules      one module per arc (C64Data/A<i>.lean) + Glob + list
"""
import argparse, base64, gzip, json, math, os, random, sys
from fractions import Fraction as F

# P = 80 bits (64 for 30/23): at 64 bits the ball for S(z_c) is too wide for the sign test Re(conj(v) S(z_c)) <= 0
# on 25/19 tile-arc records whose v is within ~1e-16 (relative) of that boundary; the nearest one is 1.3e-17 away.
P, NT, KT, D, DE, DT, DW, ES, EQ = 80, 18, 3, 23, 8, 7, 30, 13, 12


# The certificate generator's crossing radius (check_three_level_m.py r_bound, arb at 80 bits), proposed to the
# checker as rX (units 2^-P, rounded up); the checker uses max(its own proved radius, rX), so rX is not trusted.
_FL = None


def r_ship(T1, s0, s1, sc, tau_val):
    global _FL
    import flint
    from flint import arb, acb, fmpq
    if _FL is None:
        flint.ctx.prec = 80
        _FL = arb.pi()
    PI = _FL
    A = lambda q: arb(fmpq(F(q).numerator, F(q).denominator))
    def ell_ball(e, a0, a1):
        cr, ci, a, b = e
        sq = A(a0).union(A(a1))
        return acb(A(cr) + A(a) * (2 * sq).cos_pi(), A(ci) + A(b) * (2 * sq).sin_pi())
    def S(z):
        return (PI * z).sin() / (PI * z)
    def dS(z):
        return (PI * z * (PI * z).cos() - (PI * z).sin()) / (PI * z * z)
    tau = A(tau_val)
    Z = ell_ball(T1, s0, s1)
    zc = ell_ball(T1, sc, sc)
    d = arb((Z - zc).abs_upper())
    Y = arb(max(Z.imag.abs_upper(), zc.imag.abs_upper()))
    Smin = S(Z).abs_lower()
    if not Smin > 0:
        return 0
    smax = tau * (PI * Y).exp() / Smin
    r = d * (tau * PI * (PI * Y).exp() + smax * arb(dS(Z).abs_upper()))
    m, e = arb(r.upper()).man_exp()
    val = F(int(m)) * (F(2) ** int(e))
    v = val * 2 ** P
    return int(-((-v.numerator) // v.denominator))     # ceiling


class BW:
    def __init__(self):
        self.v = 0
        self.pos = 0

    def nat(self, x):
        assert x >= 0
        L = x.bit_length()
        assert L < 256, L
        self.v |= L << self.pos
        self.pos += 8
        self.v |= x << self.pos
        self.pos += L

    def int(self, x):
        self.v |= (1 if x < 0 else 0) << self.pos
        self.pos += 1
        self.nat(abs(x))

    def q(self, f):
        f = F(f)
        self.int(f.numerator)
        self.nat(f.denominator)

    def lit(self):
        b = self.v.to_bytes((self.v.bit_length() + 7) // 8, "little")
        return 'nat_b64% "' + base64.b64encode(b).decode() + '"'


def qlit(f):
    f = F(f)
    return f"⟨{f.numerator}, {f.denominator}⟩"


def ilit(x):
    return f"({x})" if x < 0 else str(x)


def scale(xs):
    """integers proportional (positive factor) to the rationals xs"""
    qs = [F(x) for x in xs]
    L = 1
    for q in qs:
        L = L * q.denominator // math.gcd(L, q.denominator)
    return [int(q * L) for q in qs]


def grid(x, E):
    v = F(x) * 2 ** E
    assert v.denominator == 1, (x, E)
    return int(v)


def wit_leaf(lf, tile_idx, m, tau, rx=0):
    w = BW()
    w.nat(tile_idx[lf["tile"]])
    w.q(lf.get("tau_rep", str(tau)))
    w.nat(rx)
    w.q(lf["sigma"])
    ts, ms = lf["wrep_t"], lf["wrep_m"]
    assert len(ts) == len(ms)
    w.nat(len(ts))
    for t, mm in zip(ts, ms):
        w.q(t)
        w.q(mm)
    tas = sorted(lf["tile_arcs"], key=lambda a: F(a[0]))
    w.nat(len(tas))
    for a in tas:
        assert len(a) == 6 + 2 * m
        w.nat(grid(a[1], EQ))
        for x in scale(a[2:]):
            w.int(x)
    return w.lit()


def excl_leaf(lf, m):
    w = BW()
    ys = lf["y"]
    if m == 1 and not isinstance(ys[0], list):
        ys = [ys]
    assert len(ys) == m
    for x in scale(list(lf["v"]) + [c for y in ys for c in y]):
        w.int(x)
    return w.lit()


def tree_term(node, tile_idx, m, tau, rad):
    if "split" in node:
        kids = node["kids"]
        assert len(kids) == 4
        return f"(.split {node['split']} " + " ".join(tree_term(k, tile_idx, m, tau, rad) for k in kids) + ")"
    if node["type"] == "empty":
        return f"(.excl ({excl_leaf(node, m)}))"
    assert node["type"] == "W"
    return f"(.wit ({wit_leaf(node, tile_idx, m, tau, rad(node.get('tau_rep', str(tau))))}))"


def arc_term(a, tile_idx, tau, T1=None):
    s0, s1 = grid(a["s0"], ES), grid(a["s1"], ES)
    if a["type"] == "E":
        ur, ui = scale(a["u"])
        return f".E {s0} {s1} {ilit(ur)} {ilit(ui)}"
    sc = grid(a["sc"], ES)
    cache = {}
    def rad(tv):
        tv = F(tv)
        if tv not in cache:
            cache[tv] = r_ship(T1, F(a["s0"]), F(a["s1"]), F(a["sc"]), tv) if T1 is not None else 0
        return cache[tv]
    rX = rad(tau)
    if a["type"] == "H":
        return f".H {s0} {s1} {sc} [] [] {rX} (.wit ({wit_leaf(a, tile_idx, 0, tau, rad(a.get('tau_rep', str(tau))))}))"
    assert a["type"] == "H3" and "pcs" in a
    m = len(a["pcs"])
    pins = "[" + ", ".join(f"({qlit(p[0])}, {qlit(p[1])})" for p in a["pcs"]) + "]"
    Rs = "[" + ", ".join(qlit(R) for R in a["Rs"]) + "]"
    return f".H {s0} {s1} {sc} {pins} {Rs} {rX} {tree_term(a['tree'], tile_idx, m, tau, rad)}"


def glob_term(C, tile_names):
    c, a, b = C["T1"]
    tiles = "[" + ", ".join("(" + ", ".join(qlit(x) for x in C["tiles"][k]) + ")" for k in tile_names) + "]"
    return (f"{{ P := {P}, n := {NT}, k := {KT}, D := {D}, dE := {DE}, dT := {DT}, dW := {DW}, ES := {ES}, EQ := {EQ}, "
            f"tau := {qlit(C['tau'])}, c := {qlit(c)}, a := {qlit(a)}, b := {qlit(b)}, tiles := {tiles} }}")


HEADER = "import C64Core.Check\nimport C64Core.Load\n\nset_option maxRecDepth 100000\n\nopen C64Chk\n\n"
TESTHDR = ("set_option compiler.extract_closed false\n\n@[noinline] def runArc (g : Glob) (a : Arc) : IO Bool := pure (checkArc g a)\n\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("out")
    ap.add_argument("--test", type=int, default=0)
    ap.add_argument("--only", default="")
    ap.add_argument("--modules", action="store_true")
    ap.add_argument("--range", default="")
    args = ap.parse_args()
    if os.path.isdir(args.cert):        # output of split_cert.py
        C = json.load(open(os.path.join(args.cert, "glob.json")))
        ldr = lambda i: json.load(open(os.path.join(args.cert, "arcs", "%04d.json" % i)))
        n_arcs = C["n_arcs"]
    else:
        C = json.load(gzip.open(args.cert, "rt") if args.cert.endswith(".gz") else open(args.cert))
        A = sorted(C["arcs"], key=lambda x: F(x["s0"]))
        ldr = lambda i: A[i]
        n_arcs = len(A)
    assert C.get("variant") == "Cp"
    tau = F(C["tau"])
    cT1, aT1, bT1 = (F(x) for x in C["T1"])
    T1 = (cT1, F(0), aT1, bT1)
    tile_names = sorted(C["tiles"])
    tile_idx = {k: i for i, k in enumerate(tile_names)}
    os.makedirs(args.out, exist_ok=True)
    if args.test or args.only:
        if args.only:
            idx = [int(x) for x in args.only.split(",")]
        else:
            random.seed(1)
            idx = sorted(random.sample(range(n_arcs), args.test))
        src = [HEADER, TESTHDR, f"def glob : Glob := {glob_term(C, tile_names)}\n\n#eval checkGlob glob\n\n"]
        for i in idx:
            a = ldr(i)
            src.append(f"def a{i} : Arc := {arc_term(a, tile_idx, tau, T1)}\n")
            src.append(f"#eval show IO Unit from do\n  let t0 ← IO.monoMsNow\n  let r ← runArc glob a{i}\n"
                       f"  IO.println s!\"arc {i} {a['type']} {{r}} {{(← IO.monoMsNow) - t0}} ms\"\n\n")
        fn = os.path.join(args.out, "Test.lean")
        open(fn, "w").write("".join(src))
        print("wrote", fn, "arcs", idx)
        return
    # module mode: C64Data/Glob.lean, C64Data/A<i>.lean (one native_decide check per arc), C64Data/Arcs.lean (list)
    d = os.path.join(args.out, "C64Data")
    os.makedirs(d, exist_ok=True)
    hdr = "import C64Core.Check\nimport C64Core.Load\n\nset_option maxRecDepth 100000\n\nopen C64Chk\n\n"
    open(os.path.join(d, "Glob.lean"), "w").write(
        hdr + "namespace C64Data\n\n" + f"def glob : Glob := {glob_term(C, tile_names)}\n\n"
        "theorem globOK : checkGlob glob = true := by native_decide\n\nend C64Data\n")
    rng = range(n_arcs) if not args.range else range(*[int(x) for x in args.range.split(":")])
    for i in rng:
        a = ldr(i)
        src = (hdr.replace("import C64Core.Load\n", "import C64Core.Load\nimport C64Data.Glob\n", 1) +
               f"namespace C64Data.A{i:04d}\n\n-- arc {i}: type {a['type']}, s0 = {a['s0']}, s1 = {a['s1']}\n"
               f"def arc : Arc := {arc_term(a, tile_idx, tau, T1)}\n\n"
               f"theorem ok : checkArc C64Data.glob arc = true := by native_decide\n\nend C64Data.A{i:04d}\n")
        open(os.path.join(d, f"A{i:04d}.lean"), "w").write(src)
    print("wrote modules", rng)


if __name__ == "__main__":
    main()
