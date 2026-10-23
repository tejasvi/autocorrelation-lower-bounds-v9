# Assemble a three-level (multi-point) certificate from several generator JSONL logs (union).
#   merge_cert_m2.py CFG OUT.json.gz RUN1.jsonl [RUN2.jsonl ...]
# E arcs (level -1) from RUN1. Every arc [s0, s1] of level 0 is taken from the first run in which it passed; an arc that
# failed at level 0 in every run may be replaced by its four level-1 quarters from one run where all four passed.
# The result must tile [0, 1] with no failures.
import sys, json, gzip
from fractions import Fraction as Fr
cfg = json.load(open(sys.argv[1])); out = sys.argv[2]
runs = [[json.loads(l) for l in open(p)] for p in sys.argv[3:]]
arcs = {}
for d in runs[0]:
    if d["level"] == -1: r = d["result"]; arcs[(Fr(r["s0"]), Fr(r["s1"]))] = r
failed = set()
for L in runs:
    for d in L:
        if d["level"] != 0: continue
        ab = (Fr(d["s0"]), Fr(d["s1"])); r = d["result"]
        if "fail" in r: failed.add(ab)
        elif ab not in arcs: arcs[ab] = r
failed -= set(arcs)
for L in runs:
    lev1 = {(Fr(d["s0"]), Fr(d["s1"])): d["result"] for d in L if d["level"] == 1}
    for ab in sorted(failed):
        a, b = ab; q = [(a + (b - a)*Fr(i, 4), a + (b - a)*Fr(i + 1, 4)) for i in range(4)]
        if all(x in lev1 and "fail" not in lev1[x] for x in q):
            for x in q: arcs[x] = lev1[x]
            failed.discard(ab)
assert not failed, f"{len(failed)} arcs still failing, e.g. {sorted(failed)[:3]}"
keys = sorted(arcs)
assert keys[0][0] == 0 and keys[-1][1] == 1 and all(keys[i][1] == keys[i + 1][0] for i in range(len(keys) - 1)), "arcs do not tile [0,1]"
for (a, b) in keys: assert Fr(arcs[(a, b)]["s0"]) == a and Fr(arcs[(a, b)]["s1"]) == b
tau = Fr(cfg["tau"]); tiles = {}
for nm, t in cfg["tiles"].items():
    tiles[nm + "up"] = [str(Fr(t[0])), str(Fr(t[1])), str(Fr(t[2])), str(Fr(t[3]))]
    tiles[nm + "dn"] = [str(Fr(t[0])), str(-Fr(t[1])), str(Fr(t[2])), str(Fr(t[3]))]
cert = {"problem": "signed third autocorrelation: three-level certificate (multi-point boxes)", "variant": "Cp", "tau": str(tau),
        "T1": [str(Fr(x)) for x in cfg["T1"]], "tiles": tiles, "arcs": [arcs[k] for k in keys], "complete": True}
with gzip.open(out, "wt") as fh: json.dump(cert, fh)
print(f"wrote {out}: {len(keys)} arcs (E {sum(1 for k in keys if arcs[k]['type'] == 'E')}, H {sum(1 for k in keys if arcs[k]['type'] == 'H')}, H3 {sum(1 for k in keys if arcs[k]['type'] == 'H3')})")
