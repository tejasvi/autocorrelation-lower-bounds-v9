#!/usr/bin/env python3
"""Witness radii for the hoisted-rBound parts of the K shards (gen_kshards.py --rprime).

  rpass.py gen OUT PLAN [PLAN ...] [--batch B]   writes OUT/RP/RP_<k>.lean: for every parted unit of the plans' arcs,
                                                  #eval prints "RP <arc> <unit> <r'>" with r' = C64KChk.rBound of the leaf
  rpass.py collect OUT                            parses OUT/RP/*.out into OUT/rprime.json {arc: {unit: r'}}

The values are only proposals: each one is checked in the kernel by its leaf's uRB theorem.
"""
import glob, json, os, re, sys

def gen(out, plans, batch):
    parted = {}
    for p in plans:
        for i, a in json.load(open(p))["arcs"].items():
            if a.get("parted"):
                parted[int(i)] = a["parted"]
    arcs = sorted(parted)
    d = os.path.join(out, "RP")
    os.makedirs(d, exist_ok=True)
    nfiles = 0
    for k in range(0, len(arcs), batch):
        grp = arcs[k:k + batch]
        L = ["".join(f"import KData.A{i:04d}\n" for i in grp),
             "\nset_option maxRecDepth 100000\n\nopen C64Chk C64KChk\n\n",
             "def rpOf (g : Glob) (o : Option C64KChk.ACtx) (us : List (Tree × List (Nat × Nat × Nat))) (i : Nat) "
             "(js : List Nat) : IO Unit := do\n"
             "  match o with\n"
             "  | none => IO.println s!\"RP {i} ctx none\"\n"
             "  | some A =>\n"
             "    for j in js do\n"
             "      match us[j]? with\n"
             "      | some (.wit dat, _) =>\n"
             "        let w := rdWit dat\n"
             "        match C64KChk.rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX with\n"
             "        | some r => IO.println s!\"RP {i} {j} {r}\"\n"
             "        | none => IO.println s!\"RP {i} {j} none\"\n"
             "      | _ => IO.println s!\"RP {i} {j} notwit\"\n\n"]
        for i in grp:
            js = ", ".join(str(j) for j in parted[i])
            L.append(f"#eval rpOf KData.glob KData.A{i:04d}.ctx KData.A{i:04d}.units {i} [{js}]\n")
        open(os.path.join(d, f"RP_{k // batch:04d}.lean"), "w").write("".join(L))
        nfiles += 1
    print("arcs with parted units", len(arcs), "units", sum(len(v) for v in parted.values()), "files", nfiles)

def collect(out):
    rp, bad = {}, []
    for f in sorted(glob.glob(os.path.join(out, "RP", "*.out"))):
        for line in open(f):
            m = re.match(r"RP (\d+) (\d+) (\d+)$", line.strip())
            if m:
                rp.setdefault(m.group(1), {})[m.group(2)] = int(m.group(3))
            elif line.startswith("RP "):
                bad.append(line.strip())
    json.dump(rp, open(os.path.join(out, "rprime.json"), "w"))
    print("radii", sum(len(v) for v in rp.values()), "arcs", len(rp), "bad", len(bad), bad[:5])

if __name__ == "__main__":
    if sys.argv[1] == "gen":
        args = sys.argv[2:]
        batch = 10
        if "--batch" in args:
            k = args.index("--batch"); batch = int(args[k + 1]); args = args[:k] + args[k + 2:]
        gen(args[0], args[1:], batch)
    else:
        collect(sys.argv[2])
