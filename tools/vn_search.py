"""Numerical search for the discretized Cloninger-Steinerberger min-max value.

n bins of width h = 1/(2n) on [-1/4, 1/4], masses p_i >= 0, sum p = 1.
Band masses P_c = sum_{i+j=c} p_i p_j, c = 0..2n-2 (band c lives on an interval of length 2h).
For every band range [c1, c2]: Omega >= 2n * sum_{c=c1}^{c2} P_c / (c2 - c1 + 2).
V_n = min_p max_{c1<=c2} of the right side.  This script finds local minima (upper bounds on V_n).
"""
import os, sys, time
import numpy as np
from scipy.optimize import linprog


def windows(n):
    nb = 2 * n - 1
    c1, c2 = np.triu_indices(nb)
    w = 2.0 * n / (c2 - c1 + 2)
    return c1, c2, w


def window_values(p, c1, c2, w):
    P = np.convolve(p, p)
    S = np.concatenate([[0.0], np.cumsum(P)])
    return w * (S[c2 + 1] - S[c1])


def window_grads(p, c1, c2, w, idx):
    """Gradient of window values idx w.r.t. p: d/dp_k sum_{c in [c1,c2]} P_c = 2 sum_{c} p_{c-k}."""
    n = len(p)
    # d P_c / d p_k = 2 p_{c-k}; prefix sums over c of p_{c-k} -> cumulative of p shifted
    cp = np.concatenate([[0.0], np.cumsum(p)])  # cp[m] = sum_{t<m} p_t
    k = np.arange(n)
    a = c1[idx][:, None] - k[None, :]
    b = c2[idx][:, None] - k[None, :]
    lo = np.clip(a, 0, n)
    hi = np.clip(b + 1, 0, n)
    G = 2.0 * (cp[hi] - cp[lo])
    return w[idx][:, None] * G


def local_min(p, c1, c2, w, iters=400, rho=0.05, tol=1e-12, act_tol=0.15):
    n = len(p)
    f = window_values(p, c1, c2, w).max()
    for it in range(iters):
        vals = window_values(p, c1, c2, w)
        f = vals.max()
        idx = np.nonzero(vals >= f - act_tol)[0]
        G = window_grads(p, c1, c2, w, idx)
        # LP in (d, t): min t s.t. vals[idx] + G d <= t, sum d = 0, -p <= d, |d| <= rho
        nv = n + 1
        cobj = np.zeros(nv); cobj[-1] = 1.0
        A = np.hstack([G, -np.ones((len(idx), 1))])
        bub = -vals[idx]
        Aeq = np.zeros((1, nv)); Aeq[0, :n] = 1.0
        bounds = [(max(-pi, -rho), rho) for pi in p] + [(None, None)]
        res = linprog(cobj, A_ub=A, b_ub=bub, A_eq=Aeq, b_eq=[0.0], bounds=bounds, method="highs")
        if res.status != 0:
            rho *= 0.5
            if rho < 1e-10:
                break
            continue
        d = res.x[:n]
        pred = f - res.x[-1]
        pn = np.maximum(p + d, 0.0); pn /= pn.sum()
        fn = window_values(pn, c1, c2, w).max()
        if pred <= tol:
            break
        ratio = (f - fn) / pred
        if ratio > 0.1:
            p = pn
            if ratio > 0.75:
                rho = min(rho * 2, 0.5)
        else:
            rho *= 0.4
            if rho < 1e-10:
                break
    return p, window_values(p, c1, c2, w).max()


def main():
    n = int(sys.argv[1]); starts = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    rng = np.random.default_rng(seed)
    c1, c2, w = windows(n)
    best = (np.inf, None)
    t0 = time.time()
    for s in range(starts):
        kind = s % 3
        if kind == 0:
            p = rng.dirichlet(np.ones(n))
        elif kind == 1:
            x = (np.arange(n) + 0.5) / n * 0.5 - 0.25
            p = 1.0 / np.sqrt(np.maximum(1e-3, 0.0625 - x * x)) * np.exp(0.3 * rng.standard_normal(n))
            p /= p.sum()
        else:
            p = rng.dirichlet(0.5 * np.ones(n))
        p, f = local_min(p, c1, c2, w)
        if f < best[0]:
            best = (f, p.copy())
            print(f"n={n} start={s} f={f:.6f} t={time.time()-t0:.1f}s", flush=True)
    f, p = best
    os.makedirs("runs/vn", exist_ok=True)
    np.save(f"runs/vn/best_n{n}_s{seed}.npy", p)
    print(f"BEST n={n} V<={f:.6f}")
    print("p*n =", np.array2string(p * n, precision=3, max_line_width=200))


if __name__ == "__main__":
    main()
