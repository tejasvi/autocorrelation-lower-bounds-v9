# coarse E pass (nE = 512) at tau = 1/4 with the new T1; writes coarseE.jsonl and fine_arcs.json
import sys, json, time
sys.path.insert(0, '.')
import gen_two_level as G2
from fractions import Fraction as Fr
cfg = json.load(open('cfg25.json'))
T1 = G2.Ell((Fr(cfg["T1"][0]), Fr(0)), Fr(cfg["T1"][1]), Fr(cfg["T1"][2]))
tau = Fr(cfg["tau"]); t0 = time.time(); fine = []
with open('coarseE.jsonl', 'w') as fh:
    for j in range(512):
        r = G2.solve_E((T1, Fr(j, 512), Fr(j + 1, 512), tau))
        fh.write(json.dumps({"j": j, "result": r}) + "\n")
        if r is None: fine += list(range(8*j, 8*j + 8))
json.dump(fine, open('fine_arcs.json', 'w'))
print(f"tau {tau}: {512 - len(fine)//8} coarse E arcs, {len(fine)} fine arcs to do, {time.time()-t0:.0f}s")
