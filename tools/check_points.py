"""Exact check of the explicit mass vectors in data/vn_points/: for each file, recompute
F_n(p) = max_{c1<=c2} 2n/(c2-c1+2) * sum_{c1<=i+j<=c2} p_i p_j exactly and compare with the stored value.
Each file therefore certifies the upper bound V_n <= F_n(p).  Usage: python3 tools/check_points.py data/vn_points/*.json"""
import sys, json
from fractions import Fraction as Fr


def F_exact(q):
    n = len(q)
    P = [Fr(0)] * (2 * n - 1)
    for i in range(n):
        for j in range(n):
            P[i + j] += q[i] * q[j]
    S = [Fr(0)]
    for x in P:
        S.append(S[-1] + x)
    return max(Fr(2 * n, c2 - c1 + 2) * (S[c2 + 1] - S[c1]) for c1 in range(2 * n - 1) for c2 in range(c1, 2 * n - 1))


ok = True
for f in sys.argv[1:]:
    d = json.load(open(f))
    q = [Fr(x) for x in d["p"]]
    good = len(q) == d["n"] and all(x >= 0 for x in q) and sum(q) == 1 and F_exact(q) == Fr(d["F_n(p)"])
    ok &= good
    print(f"{f}: n={d['n']} F_n(p)={float(Fr(d['F_n(p)'])):.6f} {'OK' if good else 'MISMATCH'}")
sys.exit(0 if ok else 1)
