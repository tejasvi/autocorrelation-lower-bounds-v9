#!/usr/bin/env python3
"""Kernel-only (K) modules for the c64 checker C64Core.Check, from the output of split_cert.py.

The kernel's caches live per declaration, so memory is bounded by checking many small theorems instead of one per
arc. For each arc i:
  KData/A<i>.lean       the data; an E arc also gets `ok : checkArc glob arc = true` by `decide +kernel` here.
                        H and H3 arcs: the leaf tree, a cut of it (C64Shard.Shard) and its units.
  KData/A<i>_G<k>.lean  `decide +kernel` theorems for a run of declarations of the arc: a unit whole (`u<j>`), or the
                        parts of a big witness leaf (C64Shard.Leaf): head `u<j>h`, winding `u<j>w`, tile-arc segments
                        `u<j>s<n>` and the last records `u<j>l`.
  KData/A<i>_Ok.lean    no evaluation beyond the cut, its unit count and the arc head: the parts put together
                        (unit_of_parts, seg_step), the units joined (groups_join, balanced), `ok`.
Plus KData/Glob.lean (the parameters) and KData/GlobOK.lean (`checkGlob glob = true` by `decide +kernel`).
Nothing here is trusted: the kernel checks every module.

Cost model (kernel seconds of the Int checker; --scale for the K port): a witness leaf costs A_TA per tile arc plus
A_W (winding) and A_H (head), an exclusion leaf A_X, and every declaration A_D on top. A subtree is one unit if it
is a leaf or costs at most --unit; a witness leaf above --part is checked in parts with --seg tile arcs per segment;
declarations are packed in order into modules of at most --module seconds. The plan (kplan.json) lists every module
with its estimated cost, for the scheduler.

--checker k uses the kernel port C64KChk (C64K.KChk) with the glue of C64Shard.ShardK/LeafK; the main module
turns `C64KChk.checkArc glob arc = true` into the checker's statement by C64KChk.checkArc_eq.

usage: gen_kshards.py SPLIT_DIR OUT [--arcs 821,280] [--checker int|k] [--scale S] [--unit U] [--part P] [--seg S]
       [--module M]
"""
import argparse, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_lean_data as G
from fractions import Fraction as F

HDR = "import C64Core.Check\nimport C64Core.Load\n"
OPTS = "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n"
A_TA, A_W, A_H, A_X, A_D = 1.2, 16.0, 3.0, 0.5, 3.0


def leaves(node):
    return [l for k in node["kids"] for l in leaves(k)] if "split" in node else [node]


def lcost(lf, sc):
    return sc * (A_TA * len(lf["tile_arcs"]) + A_W + A_H) if lf["type"] == "W" else sc * A_X


def cut_of(node, unit, sc):
    """(Lean term of the cut, units as lists of leaves): a subtree is one unit if it is a leaf or costs <= unit"""
    ls = leaves(node)
    if "split" not in node or sum(lcost(l, sc) for l in ls) <= unit:
        return ".here", [ls]
    terms, units = [], []
    for k in node["kids"]:
        t, u = cut_of(k, unit, sc)
        terms.append(t)
        units += u
    return "(.down " + " ".join(terms) + ")", units


def arc_data(a, tile_idx, tau, T1, NM):
    """Lean text of the data of an H or H3 arc: tree, pins, Rs, arc, ctx, bx0; and the tree root (JSON)"""
    s0, s1, sc = G.grid(a["s0"], G.ES), G.grid(a["s1"], G.ES), G.grid(a["sc"], G.ES)
    cache = {}

    def rad(tv):
        tv = F(tv)
        if tv not in cache:
            cache[tv] = G.r_ship(T1, F(a["s0"]), F(a["s1"]), F(a["sc"]), tv)
        return cache[tv]
    rX = rad(tau)
    if a["type"] == "H":
        root = dict(a, type="W")
        tree = f"(.wit ({G.wit_leaf(a, tile_idx, 0, tau, rad(a.get('tau_rep', str(tau))))}))"
        pins, Rs = "[]", "[]"
    else:
        root = a["tree"]
        m = len(a["pcs"])
        tree = G.tree_term(a["tree"], tile_idx, m, tau, rad)
        pins = "[" + ", ".join(f"({G.qlit(p[0])}, {G.qlit(p[1])})" for p in a["pcs"]) + "]"
        Rs = "[" + ", ".join(G.qlit(R) for R in a["Rs"]) + "]"
    txt = (f"def tree : Tree := {tree}\n\n"
           f"def pins : List (Q × Q) := {pins}\n\n"
           f"def Rs : List Q := {Rs}\n\n"
           f"def arc : Arc := .H {s0} {s1} {sc} pins Rs {rX} tree\n\n"
           f"def ctx : Option {NM['actx']} := {NM['ctx']} KData.glob {s0} {s1} {sc} pins Rs {rX}\n\n"
           f"def bx0 : List (Nat × Nat × Nat) := pins.map fun _ => (0, 0, 0)\n")
    return txt, root


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("out")
    ap.add_argument("--arcs", default="")
    ap.add_argument("--checker", default="int", choices=["int", "k"])
    ap.add_argument("--scale", type=float, default=1.0)
    ap.add_argument("--unit", type=float, default=30.0)
    ap.add_argument("--part", type=float, default=40.0)
    ap.add_argument("--seg", type=int, default=10)
    ap.add_argument("--module", type=float, default=1800.0)
    ap.add_argument("--rprime", default="", help="JSON {arc: {unit: r'}} of witness radii (K only): hoisted rBound parts")
    args = ap.parse_args()
    rprime = json.load(open(args.rprime)) if args.rprime else {}
    if args.checker == "k":
        NM = dict(walk="C64KChk.walk", ctx="C64KChk.arcCtx", actx="C64KChk.ACtx", check="C64KChk.checkArc",
                  split="C64KChk.walk_split", arcH="C64KChk.checkArc_H", glob="C64KChk.checkGlob",
                  head="C64KChk.uHead", wind="C64KChk.uWind", seg="C64KChk.uSeg", last="C64KChk.uLast",
                  parts="C64KChk.unit_of_parts", step="C64KChk.seg_step", rb="C64KChk.uRB", segR="C64KChk.uSegR",
                  lastR="C64KChk.uLastR", segOfR="C64KChk.seg_of_R", lastOfR="C64KChk.last_of_R",
                  imp="import C64K.KChk\nimport C64Shard.ShardK\nimport C64Shard.LeafK\n")
    else:
        NM = dict(walk="walk", ctx="arcCtx", actx="ACtx", check="checkArc", split="walk_split", arcH="checkArc_H",
                  glob="checkGlob", head="uHead", wind="uWind", seg="uSeg", last="uLast", parts="unit_of_parts",
                  step="seg_step", imp="import C64Shard.Leaf\n")
    sc = args.scale
    C = json.load(open(os.path.join(args.cert, "glob.json")))
    ldr = lambda i: json.load(open(os.path.join(args.cert, "arcs", "%04d.json" % i)))
    assert C.get("variant") == "Cp"
    tau = F(C["tau"])
    cT1, aT1, bT1 = (F(x) for x in C["T1"])
    T1 = (cT1, F(0), aT1, bT1)
    tile_names = sorted(C["tiles"])
    tile_idx = {k: i for i, k in enumerate(tile_names)}
    idx = [int(x) for x in args.arcs.split(",")] if args.arcs else list(range(C["n_arcs"]))
    d = os.path.join(args.out, "KData")
    os.makedirs(d, exist_ok=True)
    glob_txt = f"def glob : Glob := {G.glob_term(C, tile_names)}\n"
    open(os.path.join(d, "Glob.lean"), "w").write(
        HDR + "\n" + OPTS + "\nopen C64Chk\n\nnamespace KData\n\n" + glob_txt + "\nend KData\n")
    open(os.path.join(d, "GlobOK.lean"), "w").write(
        "import KData.Glob\n" + NM["imp"] + "\n" + OPTS + "\nopen C64Chk\n\nnamespace KData\n\n"
        f"theorem globOK : {NM['glob']} glob = true := by\n  decide +kernel\n\nend KData\n")
    plan = {"modules": [], "arcs": {}}
    plan["modules"].append({"name": "GlobOK", "cost": sc * (A_W + A_D), "deps": ["Glob"]})
    W = f"(fun A => {NM['walk']} KData.glob A)"
    for i in idx:
        a = ldr(i)
        ns = f"KData.A{i:04d}"
        head = (HDR + "import C64Shard.Shard\n" + NM["imp"] + "import KData.Glob\n\n" + OPTS + "\nopen C64Chk\n\n"
                f"namespace {ns}\n\n-- arc {i}: type {a['type']}, s0 = {a['s0']}, s1 = {a['s1']}\n")
        if a["type"] == "E":
            open(os.path.join(d, f"A{i:04d}.lean"), "w").write(
                head + f"def arc : Arc := {G.arc_term(a, tile_idx, tau, T1)}\n\n"
                f"theorem ok : {NM['check']} KData.glob arc = true := by\n  decide +kernel\n\nend {ns}\n")
            plan["modules"].append({"name": f"A{i:04d}", "cost": sc * (4 * A_X + A_D), "deps": ["Glob"]})
            plan["arcs"][i] = {"ok": f"A{i:04d}"}
            continue
        txt, root = arc_data(a, tile_idx, tau, T1, NM)
        cut, units = cut_of(root, args.unit, sc)
        open(os.path.join(d, f"A{i:04d}.lean"), "w").write(
            head + txt + f"\ndef cut : Cut := {cut}\n\n"
            "def units : List (Tree × List (Nat × Nat × Nat)) := cutUnits cut tree bx0\n\n" + f"end {ns}\n")
        # declarations: (name, Lean text, cost); assemblies of parted units go to the Ok module
        U = lambda j: f"(unitsIn units {j} {j + 1}).all fun u =>"
        decls, asm, parted = [], [], []
        for j, ls in enumerate(units):
            c = sum(lcost(l, sc) for l in ls)
            if len(ls) == 1 and ls[0]["type"] == "W" and c > args.part:
                N = len(ls[0]["tile_arcs"])
                J = args.seg * ((N - 1) // args.seg)
                st = lambda body: f" : ctx.any (fun A => {U(j)} {body}) = true := by\n  decide +kernel\n\n"
                decls.append((f"u{j}h", f"theorem u{j}h" + st(f"{NM['head']} KData.glob A u"), sc * (A_H + A_D)))
                decls.append((f"u{j}w", f"theorem u{j}w" + st(f"{NM['wind']} KData.glob A u"), sc * (A_W + A_D)))
                segs = list(range(0, J, args.seg))
                rp = rprime.get(str(i), {}).get(str(j)) if args.checker == "k" else None
                parted.append(j)
                if rp is not None:          # hoisted rBound: one radius theorem, parts with the literal radius
                    decls.append((f"u{j}r", f"theorem u{j}r" + st(f"{NM['rb']} KData.glob A {rp} u"), sc * A_D))
                    for n, s in enumerate(segs):
                        decls.append((f"u{j}s{n}", f"theorem u{j}s{n}" +
                                      st(f"{NM['segR']} KData.glob A {s} {args.seg} {rp} u"), sc * (A_TA * args.seg + A_D)))
                    decls.append((f"u{j}l", f"theorem u{j}l" + st(f"{NM['lastR']} KData.glob A {J} {N - J} {rp} u"),
                                  sc * (A_TA * (N - J) + A_D)))
                    t = f"({NM['lastOfR']} u{j}r u{j}l)"
                    for n in reversed(range(len(segs))):
                        t = f"({NM['step']} ({NM['segOfR']} u{j}r u{j}s{n}) {t})"
                else:
                    for n, s in enumerate(segs):
                        decls.append((f"u{j}s{n}", f"theorem u{j}s{n}" + st(f"{NM['seg']} KData.glob A {s} {args.seg} u"),
                                      sc * (A_TA * args.seg + A_D)))
                    decls.append((f"u{j}l", f"theorem u{j}l" + st(f"{NM['last']} KData.glob A {J} {N - J} u"),
                                  sc * (A_TA * (N - J) + A_D)))
                    t = f"u{j}l"
                    for n in reversed(range(len(segs))):
                        t = f"({NM['step']} u{j}s{n} {t})"
                asm.append(f"theorem u{j} : ctx.any (fun A => {U(j)} {NM['walk']} KData.glob A u.1 u.2) = true :=\n"
                           f"  {NM['parts']} u{j}h u{j}w {t}\n\n")
            else:
                decls.append((f"u{j}", f"theorem u{j} : ctx.any (fun A => {U(j)} {NM['walk']} KData.glob A u.1 u.2) ="
                              f" true := by\n  decide +kernel\n\n", c + sc * A_D))
        mods, cur, cc = [], [], 0.0
        for dcl in decls:
            if cur and cc + dcl[2] > args.module:
                mods.append(cur)
                cur, cc = [], 0.0
            cur.append(dcl)
            cc += dcl[2]
        mods.append(cur)
        for k, md in enumerate(mods):
            open(os.path.join(d, f"A{i:04d}_G{k:03d}.lean"), "w").write(
                f"import {ns}\n\n{OPTS}\nopen C64Chk\n\nnamespace {ns}\n\n" + "".join(x[1] for x in md) + f"end {ns}\n")
            plan["modules"].append({"name": f"A{i:04d}_G{k:03d}", "cost": sum(x[2] for x in md),
                                    "deps": [f"A{i:04d}"], "decls": len(md)})

        def join(lo, hi):
            if hi - lo == 1:
                return f"u{lo}"
            mid = (lo + hi) // 2
            return (f"(groups_join ctx {W} units (a := {lo}) (b := {mid}) (c := {hi}) (by decide) (by decide)\n"
                    f"      {join(lo, mid)}\n      {join(mid, hi)})")
        imports = "".join(f"import {ns}_G{k:03d}\n" for k in range(len(mods)))
        open(os.path.join(d, f"A{i:04d}_Ok.lean"), "w").write(
            imports + f"\n{OPTS}\nopen C64Chk\n\nnamespace {ns}\n\n" + "".join(asm) +
            f"theorem walkOK : ctx.any (fun A => {NM['walk']} KData.glob A tree bx0) = true :=\n"
            f"  arc_of_groups ctx {W} (fun A => {NM['split']} KData.glob A) cut tree bx0 {len(units)}\n"
            f"    (by decide +kernel) (by decide +kernel)\n    {join(0, len(units))}\n\n"
            f"theorem ok : {NM['check']} KData.glob arc = true := by\n"
            f"  unfold arc\n  exact {NM['arcH']} (by decide +kernel) walkOK\n\nend {ns}\n")
        plan["modules"].append({"name": f"A{i:04d}", "cost": 0.0, "deps": ["Glob"]})
        plan["modules"].append({"name": f"A{i:04d}_Ok", "cost": sc * (A_H + 2 * A_D),
                                "deps": [f"A{i:04d}_G{k:03d}" for k in range(len(mods))]})
        plan["arcs"][i] = {"ok": f"A{i:04d}_Ok", "units": len(units), "decls": len(decls), "groups": len(mods),
                           "cost": sum(x[2] for x in decls), "parted": parted}
    json.dump(plan, open(os.path.join(args.out, "kplan.json"), "w"))
    tot = sum(m["cost"] for m in plan["modules"])
    print("arcs", len(idx), "modules", len(plan["modules"]), "est kernel CPU-h %.1f" % (tot / 3600),
          "max module s %.0f" % max(m["cost"] for m in plan["modules"]))


if __name__ == "__main__":
    main()
