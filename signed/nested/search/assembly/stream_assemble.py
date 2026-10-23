# Streaming assembly of the production certificate (bounded memory):
#   inputs: coarseE.jsonl, phase-A outputs (A_*.jsonl), phase-B outputs (B_*.jsonl)
#   outputs: OUT_FULL.json.gz (the certificate) and NS subset certificates OUT_SUB_###.json.gz (arc i -> subset i % NS),
#            same header, for sharded --subset checks; prints a coverage summary
# usage: stream_assemble.py CFG TAU coarseE.jsonl 'A_glob' 'B_glob' WORKDIR OUT_FULL NS OUT_SUB_PREFIX
import sys, os, json, gzip, glob
from fractions import Fraction
cfg = json.load(open(sys.argv[1])); tau = sys.argv[2]; coarse = sys.argv[3]; Ag = sys.argv[4]; Bg = sys.argv[5]
wd = sys.argv[6]; out_full = sys.argv[7]; ns = int(sys.argv[8]); out_sub = sys.argv[9]
os.makedirs(wd, exist_ok=True)
E = {}
for l in open(coarse):
    r = json.loads(l); E[r["j"]] = r["result"]
assert len(E) == 512
fine = {}; stubs = {}
for fn in sorted(glob.glob(Ag)):
    for l in open(fn):
        r = json.loads(l); k = r["k"]; assert isinstance(k, int)
        if "stub" in r: stubs[k] = r
        else:
            assert "fail" not in r["result"], f"phase A failure at {k}"
            fine[k] = r["result"]
# phase B entries -> one temp file per arc (append), keyed by (q0, q1)
fh_cache = {}
nb = 0; nfail = 0
for fn in sorted(glob.glob(Bg)):
    for l in open(fn):
        r = json.loads(l); k = r["k"]
        if not r["ok"]: nfail += 1; continue
        f = fh_cache.get(k)
        if f is None:
            if len(fh_cache) > 400:
                for x in fh_cache.values(): x.close()
                fh_cache.clear()
            f = open(os.path.join(wd, f"arc_{k}.jsonl"), "a"); fh_cache[k] = f
        f.write(json.dumps({"q0": r["q0"], "q1": r["q1"], "entries": r["entries"]}) + "\n"); nb += 1
for x in fh_cache.values(): x.close()
print(f"phase B lines ok {nb}, failed {nfail}", flush=True)
tiles = {}
for nm, t in cfg["tiles"].items():
    tiles[nm + "up"] = t; tiles[nm + "dn"] = [t[0], str(-Fraction(t[1])), t[2], t[3]]
head = '{"variant": "Cp", "tau": ' + json.dumps(tau) + ', "T1": ' + json.dumps(cfg["T1"]) + ', "tiles": ' + json.dumps(tiles) + \
       ', "iv_eps": "1/1000000", "arcs": ['
F = gzip.open(out_full, "wt"); F.write(head)
SUB = [gzip.open(f"{out_sub}_{i:03d}.json.gz", "wt") for i in range(ns)]
for x in SUB: x.write(head)
first_full = True; first_sub = [True]*ns; idx = 0; missing = []; counts = {"E": 0, "N": 0, "joined": 0}
def emit(arc):
    global first_full, idx
    s = json.dumps(arc)
    F.write(("" if first_full else ",") + s); first_full = False
    i = idx % ns; SUB[i].write(("" if first_sub[i] else ",") + s); first_sub[i] = False
    idx += 1; counts[arc["type"]] = counts.get(arc["type"], 0) + 1
for j in range(512):
    if E[j] is not None: emit(E[j]); continue
    for k in range(8*j, 8*j + 8):
        if k in fine: emit(fine[k]); continue
        if k not in stubs: missing.append(k); continue
        have = {}
        p = os.path.join(wd, f"arc_{k}.jsonl")
        if os.path.exists(p):
            for l in open(p):
                r = json.loads(l); have[(Fraction(r["q0"]), Fraction(r["q1"]))] = r["entries"]
        # each original task piece must be tiled exactly by result pieces (a piece may have been split into sub-pieces)
        pieces = sorted(have)
        ent = []; ok = True
        for q0s, q1s in stubs[k]["tasks"]:
            q0, q1 = Fraction(q0s), Fraction(q1s)
            sub = [pc for pc in pieces if q0 <= pc[0] and pc[1] <= q1]
            if (q0, q1) in have:
                ent += have[(q0, q1)]; continue
            cur = q0; chain = []
            for a, b in sub:
                if a == cur: chain.append((a, b)); cur = b
            if cur != q1: ok = False; break
            for pc in chain: ent += have[pc]
        if not ok:
            missing.append(k); continue
        st = stubs[k]["stub"]; leaf = {kk: v for kk, v in st.items() if kk not in ("stub", "w1_arcs", "hard")}
        leaf["tile_arcs"] = st["w1_arcs"] + ent
        s0, s1 = Fraction(k, 4096), Fraction(k + 1, 4096)
        emit({"type": "N", "s0": str(s0), "s1": str(s1), "sc": str((s0 + s1)/2), "pcs": [], "Rs": [], "tree": leaf}); counts["joined"] += 1
F.write("]}"); F.close()
for x in SUB: x.write("]}"); x.close()
print(f"arcs written {idx}: {counts}; missing {len(missing)}: {missing[:20]}")
sys.exit(1 if missing else 0)
