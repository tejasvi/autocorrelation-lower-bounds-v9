# split3: V23 pieces that failed at the 20,000-node budget (index rows from the V23 workers *-w with ok false) -> 16 equal q-pieces
# each (same rule as split1/split2; tile, ts, ms copied from the failed piece's task line in split1/split2_tasks.jsonl).
# Writes split3_parents.txt and split3_tasks.jsonl.
import json
from fractions import Fraction
R = ''
lines = {}
for fn in ('split1_tasks.jsonl', 'split2_tasks.jsonl'):
    for l in open(R + fn):
        d = json.loads(l); lines[(d['k'], d['q0'], d['q1'])] = d
ok = set(); bad = []
for l in open(R + 'done_index.tsv'):
    f = l.rstrip('\n').split('\t'); key = (int(f[0]), f[1], f[2])
    if f[3] == 'true': ok.add(key)
    elif f[5].endswith('-w'): bad.append(key)
bad = sorted(set(k for k in bad if k not in ok))
par = []; out = []
for key in bad:
    t = lines[key]; par.append(json.dumps([t['k'], t['q0'], t['q1']]))
    q0, q1 = Fraction(t['q0']), Fraction(t['q1'])
    for i in range(16):
        t2 = dict(t); t2['q0'] = str(q0 + (q1 - q0)*i/16); t2['q1'] = str(q0 + (q1 - q0)*(i + 1)/16)
        out.append(json.dumps(t2))
assert len(set(out)) == len(out) == 16*len(bad)
open(R + 'split3_parents.txt', 'w').write('\n'.join(par) + '\n')
open(R + 'split3_tasks.jsonl', 'w').write('\n'.join(out) + '\n')
print('parents', len(par), 'sub-tasks', len(out))
