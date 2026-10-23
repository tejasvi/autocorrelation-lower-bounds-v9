"""Wider global search for V_n: random restarts + perturbation (basin hopping) from the incumbent."""
import os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vn_search import windows, window_values, local_min

n = int(sys.argv[1]); starts = int(sys.argv[2]); seed = int(sys.argv[3])
rng = np.random.default_rng(seed)
c1, c2, w = windows(n)
best_f, best_p = np.inf, None
t0 = time.time()
for s in range(starts):
    if best_p is not None and s % 2 == 1:
        # perturb incumbent: multiplicative noise + random mass moves
        p = best_p * np.exp(0.5 * rng.standard_normal(n))
        k = rng.integers(0, n, size=3); p[k] += rng.uniform(0, 0.05, size=3)
        p = np.maximum(p, 0); p /= p.sum()
    else:
        a = rng.choice([0.3, 0.6, 1.0, 2.0])
        p = rng.dirichlet(a * np.ones(n))
    p, f = local_min(p, c1, c2, w)
    if f < best_f - 1e-9:
        best_f, best_p = f, p.copy()
        print(f"n={n} seed={seed} start={s} f={f:.6f} t={time.time()-t0:.0f}s", flush=True)
os.makedirs("runs/vn", exist_ok=True)
np.save(f"runs/vn/glob_n{n}_s{seed}.npy", best_p)
print(f"BEST n={n} seed={seed} V<={best_f:.6f}")
