"""mk_tamper.py SRC OUTDIR: tampered copies of a tree-only certificate (one directory per variant).

Variants (each changes one thing; the verifier must reject every one):
  drop_leaf_mid   one U record removed from the middle of a job
  drop_leaf_end   the last record of a job removed
  extra_record    one U record appended to a job
  split_header    a job's header path value moved by 2^-30 (its region no longer matches the delegating S)
  split_out       an I record's value moved outside (L_b, U_b)
  split_moved     the root job's first I split moved inside its interval (all later records keep their values)
  lam_meta        meta.json lam raised (job headers keep the old value)
  lam_all         lam raised in meta.json and in every job header (consistent, mathematically too strong)
  sym_removed     the ("sym",) row (half-space hypothesis) removed from meta.rowkeys
  sym_malformed   the ("sym",) row key replaced by ["sym", 1]
  job_dropped     one delegated job file removed
  job_duplicated  one job file duplicated under another name
  leaf_to_S       one U record replaced by an S record (delegation to a job that does not exist)
"""
import sys, os, json, gzip, glob, shutil, random
from fractions import Fraction

src, out = sys.argv[1], sys.argv[2]
rng = random.Random(20261020)
meta = json.load(open(os.path.join(src, 'meta.json')))
files = sorted(glob.glob(os.path.join(src, 'jobs', '*.jsonl.gz')))


def read(f):
    with gzip.open(f, 'rt') as fh:
        return [line.rstrip('\n') for line in fh]


def write(f, lines):
    with gzip.open(f, 'wt') as fh:
        fh.write('\n'.join(lines) + '\n')


def variant(name, meta_new=None):
    d = os.path.join(out, name)
    if os.path.exists(d):
        shutil.rmtree(d)
    os.makedirs(os.path.join(d, 'jobs'))
    for f in files:
        shutil.copyfile(f, os.path.join(d, 'jobs', os.path.basename(f)))
    json.dump(meta if meta_new is None else meta_new, open(os.path.join(d, 'meta.json'), 'w'))
    return d


def jpath(d, f):
    return os.path.join(d, 'jobs', os.path.basename(f))


root = [f for f in files if json.loads(read(f)[0])['path'] == []][0]
big = sorted(files, key=lambda f: -len(read(f)))[0]
nonroot = [f for f in files if f != root]
log = {}

d = variant('drop_leaf_mid'); L = read(big)
ui = [i for i, s in enumerate(L) if s.startswith('["U"')]
k = ui[len(ui) // 2]; del L[k]; write(jpath(d, big), L); log['drop_leaf_mid'] = f'{os.path.basename(big)} line {k + 1}'

d = variant('drop_leaf_end'); L = read(big)
log['drop_leaf_end'] = f'{os.path.basename(big)} last line {L[-1]}'; del L[-1]; write(jpath(d, big), L)

d = variant('extra_record'); L = read(big); L.append('["U"]'); write(jpath(d, big), L); log['extra_record'] = os.path.basename(big)

d = variant('split_header'); f = rng.choice(nonroot); L = read(f); h = json.loads(L[0])
b, s, side = h['path'][-1]; s2 = Fraction(s) + Fraction(1, 2 ** 30); h['path'][-1] = [b, str(s2), side]
L[0] = json.dumps(h); write(jpath(d, f), L); log['split_header'] = f'{os.path.basename(f)} last path entry {s} -> {s2}'

d = variant('split_out'); L = read(big)
ii = [i for i, s in enumerate(L) if s.startswith('["I"')]
k = ii[len(ii) // 3]; r = json.loads(L[k]); old = r[2]; r[2] = '1'      # m_b <= 1 always, so s = 1 is never strictly inside
L[k] = json.dumps(r); write(jpath(d, big), L); log['split_out'] = f'{os.path.basename(big)} line {k + 1}: {old} -> 1'

d = variant('split_moved'); L = read(root)
k = [i for i, s in enumerate(L) if s.startswith('["I"')][0]; r = json.loads(L[k]); old = Fraction(r[2])
r[2] = str(old * Fraction(3, 4)); L[k] = json.dumps(r); write(jpath(d, root), L)
log['split_moved'] = f'root job {os.path.basename(root)} line {k + 1}: block {r[1]} {old} -> {r[2]}'

lam2 = str(Fraction(meta['lam']) + Fraction(1, 100))
m2 = dict(meta); m2['lam'] = lam2; variant('lam_meta', m2); log['lam_meta'] = f"{meta['lam']} -> {lam2} in meta.json only"

d = variant('lam_all', m2)
for f in files:
    L = read(f); h = json.loads(L[0]); h['lam'] = lam2; L[0] = json.dumps(h); write(jpath(d, f), L)
log['lam_all'] = f"{meta['lam']} -> {lam2} everywhere"

m3 = dict(meta); m3['rowkeys'] = [k for k in meta['rowkeys'] if k != ['sym']]
assert len(m3['rowkeys']) == len(meta['rowkeys']) - 1
variant('sym_removed', m3); log['sym_removed'] = 'meta.rowkeys without ["sym"]'

m4 = dict(meta); m4['rowkeys'] = [(['sym', 1] if k == ['sym'] else k) for k in meta['rowkeys']]
variant('sym_malformed', m4); log['sym_malformed'] = '["sym"] -> ["sym", 1]'

d = variant('job_dropped'); f = rng.choice(nonroot); os.remove(jpath(d, f)); log['job_dropped'] = os.path.basename(f)

d = variant('job_duplicated'); f = rng.choice(nonroot)
shutil.copyfile(f, os.path.join(d, 'jobs', 'ffffffffffffffffffffffffffffffff.jsonl.gz')); log['job_duplicated'] = os.path.basename(f)

d = variant('leaf_to_S'); L = read(big)
ui = [i for i, s in enumerate(L) if s.startswith('["U"')]
k = ui[len(ui) // 4]; L[k] = '["S"]'; write(jpath(d, big), L); log['leaf_to_S'] = f'{os.path.basename(big)} line {k + 1}'

json.dump(log, open(os.path.join(out, 'TAMPER_LOG.json'), 'w'), indent=1)
for k, v in log.items():
    print(f'{k:16s} {v}')
