"""Unit tests for iv_core / iv_lp (run: python3 test_core.py CERTDIR)."""
import sys, os, json, random
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import iv_core as C
import iv_lp as P

certdir = sys.argv[1]
meta = json.load(open(os.path.join(certdir, 'meta.json')))
n = meta['n']; lam = C.rational(meta['lam'])
T = C.Blocks(n)

# (1) numbering against the recursive definition of section 3
ref = []
def build(lo, hi):
    me = len(ref); ref.append([lo, hi, []])
    if hi - lo > 1:
        mid = (lo + hi) // 2
        ref[me][2].append(build(lo, mid)); ref[me][2].append(build(mid, hi))
    return me
build(0, n)
assert all(ref[b][0] == T.lo[b] and ref[b][1] == T.hi[b] and ref[b][2] == T.kids[b] for b in range(T.nB)), 'numbering'
print('(1) block numbering matches the recursive preorder definition; nB =', T.nB)

# (2) row validity at true points of random p in random regions containing them
rows = C.Rows(T, meta['rowkeys'])
rng = random.Random(1)
def true_point(p):
    m = [sum(p[T.lo[b]:T.hi[b]]) for b in range(T.nB)]
    x = {('m', b): m[b] for b in range(T.nB)}
    for i in range(n):
        for j in range(i, n):
            x[('Z', i, j)] = p[i] * p[j]
    for d in range(T.nB):
        for e in range(d, T.nB):
            c = T.pair(d, e)
            if c[0] == 'ZA':
                x[c] = m[d] * m[e]
    P_ = [sum(p[i] * p[c - i] for i in range(n) if 0 <= c - i < n) for c in range(2 * n - 1)]
    G = []; s = Fraction(0)
    for c in range(2 * n - 1):
        s += P_[c]; G.append(s); x[('P', c)] = P_[c]; x[('G', c)] = s
    F = max(Fraction(2 * n, c2 - c1 + 2) * (G[c2] - (G[c1 - 1] if c1 else 0)) for c1 in range(2 * n - 1) for c2 in range(c1, 2 * n - 1))
    x[('t',)] = F
    return x, m
viol = 0; checked = 0
for trial in range(30):
    w = [Fraction(rng.randint(0, 50)) for _ in range(n)]
    if sum(w) == 0:
        continue
    p = [v / sum(w) for v in w]
    if sum((2 * i - (n - 1)) * p[i] for i in range(n)) > 0:
        p = p[::-1]
    x, m = true_point(p)
    # random region containing m: bounds at multiples of 2^-10 around m
    L = [max(Fraction(0), Fraction(int(mb * 1024) - rng.randint(0, 40), 1024)) for mb in m]
    U = [min(Fraction(1), Fraction(int(mb * 1024) + 1 + rng.randint(0, 40), 1024)) for mb in m]
    reg = C.propagate(T, L, U)
    assert reg is not None and all(reg[0][b] <= m[b] <= reg[1][b] for b in range(T.nB)), 'propagation lost the point'
    for r in range(len(rows.keys)):
        lo, up, ent = rows.row(r, reg[0], reg[1])
        val = sum(a * x[c] for c, a in ent.items())
        checked += 1
        if (lo is not None and val < lo) or (up is not None and val > up):
            viol += 1
    for _ in range(20):
        d, e = rng.randrange(1, T.nB), rng.randrange(1, T.nB)
        key = ['sq', rng.randint(-9, 9), [[d, rng.randint(-9, 9)]] + ([[e, rng.randint(-9, 9)]] if e != d else [])]
        try:
            lo, up, ent = C.square_cut(T, key)
        except C.SpecError:
            continue
        val = sum(a * x[c] for c, a in ent.items()); checked += 1
        if val < lo:
            viol += 1
print(f'(2) row validity at true points: {checked} row evaluations, {viol} violations')

# (3) exact NS bound vs the LP optimum, and the dual sign convention
orc = P.Oracle(T, rows)
reg = C.root_region(T)
for trial in range(12):
    b = rng.randrange(1, T.nB)
    s = Fraction(rng.randint(1, 1023), 1024)
    ch = C.split(T, reg, b, s, rng.randint(0, 1)) if reg[0][b] < s < reg[1][b] else reg
    if ch is None:
        continue
    orc.set_region(ch)
    res = orc.solve()
    if res is None:
        print(f'(3) region split at block {b}: LP not optimal (skipped)'); continue
    if isinstance(res, str):
        ray = orc.farkas()
        v = None if ray is None else P.exact_farkas_value(orc, ch, ray)
        print(f'(3) region split at block {b}: LP infeasible; exact Farkas value {None if v is None else float(v)} (> 0 proves emptiness)')
        continue
    obj, x, y = res
    lb = P.exact_leaf_bound(orc, ch, y)
    print(f'(3) region split at block {b}: LP objective {obj:.10f}, exact NS bound {float(lb):.10f}, diff {obj - float(lb):.2e}')
    reg = ch

# (4) the lazy oracle: after row generation its LP value equals the full LP value, and the exact bound matches it
lorc = P.LazyOracle(T, rows, lam, objbound=None)
reg = C.root_region(T)
for trial in range(10):
    b = rng.randrange(1, T.nB)
    s = Fraction(rng.randint(1, 1023), 1024)
    ch = C.split(T, reg, b, s, rng.randint(0, 1)) if reg[0][b] < s < reg[1][b] else reg
    if ch is None:
        continue
    orc.set_region(ch); lorc.set_region(ch)
    full = orc.solve()
    while True:
        res = lorc.solve()
        if isinstance(res, str) or res is None:
            break
        add = lorc.violated(res[1])
        if not add:
            break
        lorc.add_rows(add)
    if isinstance(full, str) or isinstance(res, str) or full is None or res is None:
        print(f'(4) block {b}: full {full if isinstance(full, str) else "ok"}, lazy {res if isinstance(res, str) else "ok"}')
        continue
    lb = lorc.exact_bound(ch, res[2])
    print(f'(4) block {b}: full LP {full[0]:.10f}, lazy LP {res[0]:.10f} ({len(lorc.lp)} rows), exact {float(lb):.10f}')
    reg = ch
