# split2 manifest (same check as split1_manifest_check.py): every redo parent task piece -> its 16 child pieces, and a check with the frozen assembler's coverage rule
# (stream_assemble 8ef058b0: for each original task piece (q0, q1) of a stub, the result pieces inside it must chain exactly
# from q0 to q1, consecutive pieces sharing endpoints; Fraction arithmetic).  Writes split2_manifest.jsonl and prints a verdict.
import json, collections
from fractions import Fraction
R = ''
parents = [tuple(json.loads(l)) for l in open(R + 'split2_parents.txt')]
kids = collections.defaultdict(list); tiles = {}
for l in open(R + 'split2_tasks.jsonl'):
    t = json.loads(l); kids[t['k']].append((Fraction(t['q0']), Fraction(t['q1']))); tiles[t['k']] = t['tile']
up = {}
for l in open('tasks_up_t25.jsonl'):
    t = json.loads(l); up[(t['k'], t['q0'], t['q1'])] = t
bad = 0; n = 0
with open(R + 'split2_manifest.jsonl', 'w') as fh:
    for (k, q0s, q1s) in parents:
        par = up[(k, q0s, q1s)]; q0, q1 = Fraction(q0s), Fraction(q1s)
        # the assembler's rule, verbatim in substance: pieces inside [q0, q1], chained from q0
        sub = sorted(pc for pc in kids[k] if q0 <= pc[0] and pc[1] <= q1)
        cur = q0; chain = []
        for a, b in sub:
            if a == cur: chain.append((a, b)); cur = b
        ok = (cur == q1 and len(chain) == 16 and all(b > a for a, b in chain))
        # children must also match the queued sub-task specs exactly (same tile, ts, ms as the parent)
        bad += not ok; n += 1
        fh.write(json.dumps({"parent": [k, q0s, q1s], "tile": par["tile"], "children": [[str(a), str(b)] for a, b in chain], "tiling_ok": ok}) + "\n")
# every queued sub-task must belong to exactly one parent and carry the parent's tile/ts/ms
pk = collections.defaultdict(list)
for (k, q0s, q1s) in parents: pk[k].append((Fraction(q0s), Fraction(q1s), up[(k, q0s, q1s)]))
orphan = 0; mism = 0
for l in open(R + 'split2_tasks.jsonl'):
    t = json.loads(l); a, b = Fraction(t['q0']), Fraction(t['q1'])
    own = [p for p in pk[t['k']] if p[0] <= a and b <= p[1]]
    if len(own) != 1: orphan += 1; continue
    p = own[0][2]
    if (t['tile'], t['ts'], t['ms']) != (p['tile'], p['ts'], p['ms']): mism += 1
print(f"parents {n}, tiling failures {bad}, sub-tasks without exactly one parent {orphan}, tile/rep mismatches {mism}")
print("VERDICT", "PASS" if bad == 0 and orphan == 0 and mism == 0 else "FAIL")
