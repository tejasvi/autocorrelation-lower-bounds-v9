"""Independent exact check of the CS window bound for a given mass vector (brute force over windows)."""
import sys
from fractions import Fraction as Fr
import numpy as np
p = np.load(sys.argv[1]); n = len(p)
q = [Fr(float(x)) for x in p]; s = sum(q); q = [x / s for x in q]       # exact rational, normalized
h = Fr(1, 2 * n)
best = Fr(0); arg = None
for start in range(0, 2 * n):            # window [-1/2 + start h, -1/2 + (start+L) h]
    for L in range(1, 2 * n - start + 1):
        tot = Fr(0)
        for i in range(n):
            for j in range(n):
                lo = i + j; hi = i + j + 2           # B_i + B_j = [-1/2 + (i+j)h, -1/2 + (i+j+2)h]
                if start <= lo and hi <= start + L:
                    tot += q[i] * q[j]
        val = tot / (L * h)
        if val > best: best, arg = val, (start, L)
print(f"n={n} exact max window bound = {float(best):.6f} at window {arg}")
