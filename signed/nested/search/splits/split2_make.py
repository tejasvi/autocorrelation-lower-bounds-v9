# split2: the 26 requeued band tasks held by one queue worker (its claims after a server restart) -> 16 equal q-pieces each, the same
# rule as split1 and as qserver's SPLIT option (q0 + (q1 - q0)*i/16, Fraction strings).  Inputs: claims_11b.txt (the server's claim
# lines for that worker).  Writes split2_parents.txt and split2_tasks.jsonl; refuses parents that are not upper-half tasks.
import json
from fractions import Fraction
R = ''
up = {}
for l in open('tasks_up_t25.jsonl'):
    t = json.loads(l); up[(t['k'], t['q0'], t['q1'])] = t
par = []; out = []
for l in open(R + 'claims_11b.txt'):
    t = json.loads(l.split('\t', 1)[1]); key = (t['k'], t['q0'], t['q1'])
    assert up[key] == t, key
    par.append(json.dumps([t['k'], t['q0'], t['q1']]))
    q0, q1 = Fraction(t['q0']), Fraction(t['q1'])
    for i in range(16):
        t2 = dict(t); t2['q0'] = str(q0 + (q1 - q0)*i/16); t2['q1'] = str(q0 + (q1 - q0)*(i + 1)/16)
        out.append(json.dumps(t2))
assert len(set(par)) == len(par) == 26 and len(set(out)) == len(out) == 416
open(R + 'split2_parents.txt', 'w').write('\n'.join(par) + '\n')
open(R + 'split2_tasks.jsonl', 'w').write('\n'.join(out) + '\n')
print('parents', len(par), 'sub-tasks', len(out))
