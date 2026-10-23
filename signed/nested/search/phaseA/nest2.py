# Faster nested-crossing prototype (float, NOT rigorous): early-exit tile scans in bit-reversal order, last-success tile first,
# adaptive bisection of hard arcs starting from whole hard intervals.  Reuses the LPs of nest_proto.py.
import numpy as np, os
import nest_proto as NP

def bitrev_order(N):
    b = int(np.log2(N)); idx = np.arange(N)
    rev = np.zeros(N, dtype=int)
    for i in range(b): rev |= ((idx >> i) & 1) << (b - 1 - i)
    return rev

ORD = {}
LAST_HARD = {}
def scan(tile, nmkey, discs, tau, N=512, early=True):
    """W1 margins at N midpoints; early: stop at the first hard sample (bit-reversal order, last hard location first).
    Returns (hard_intervals or None if early-stopped with a hard point found, nlp, min margin)."""
    if N not in ORD: ORD[N] = bitrev_order(N)
    order = list(ORD[N])
    if early and nmkey in LAST_HARD:
        k0 = int(LAST_HARD[nmkey]*N) % N; order = [k0] + [k for k in order if k != k0]
    mg = np.full(N, np.nan); nlp = 0
    for k in order:
        q = (k + 0.5)/N
        r = NP.w1_lp(tile.zf(q), discs, tau); nlp += 1
        mg[k] = -1.0 if r is None else r[1]
        if mg[k] <= 1e-7:
            LAST_HARD[nmkey] = q
            if early: return None, nlp, None
    hard = mg <= 1e-7
    iv = []; k = 0
    while k < N:
        if hard[k]:
            j = k
            while j + 1 < N and hard[j + 1]: j += 1
            iv.append((k/N, (j + 1)/N, float(mg[k:j+1].min()))); k = j + 1
        else: k += 1
    pos = mg[~hard]
    return iv, nlp, (float(pos.min()) if pos.size else None)

STATS = {}
LAST_TILE = {}
NODE_BUDGET = int(os.environ.get("NODE_BUDGET", "100000"))
R_NEST = float(os.environ.get("R_NEST", "0.02"))
RMAX = float(os.environ.get("RMAX", "0.3"))
NFULL = int(os.environ.get("NFULL", "512"))
def bump(k, v=1): STATS[k] = STATS.get(k, 0) + v

def solve(discs, tau, tiles, nest, maxnest, tag, log, r_self=0.0, minarc=2**-22):
    bump('nodes')
    if STATS['nodes'] > NODE_BUDGET: raise RuntimeError("node budget")
    rr = NP.rep_lp(discs)
    if rr is None or rr[2] > tau:
        bump('empty'); log(f"{tag} EMPTY"); return True
    w0 = rr[0]
    odd = [nm for nm, tl in tiles.items() if (lambda n: n is not None and n % 2 == 1)(NP.winding(tl, w0))]
    if not odd:
        bump('fail'); log(f"{tag} FAIL no odd tile"); return False
    lt = LAST_TILE.get(nest)
    pref = ([lt] if lt in odd else []) + [nm for nm in odd if nm != lt]
    for nm in pref[:4]:
        iv, nlp, mpos = scan(tiles[nm], (nest, nm), discs, tau, N=NFULL, early=True)
        bump('lps', nlp)
        if iv is not None and not iv:
            bump('W'); LAST_TILE[nest] = nm
            log(f"{tag} W {nm} (rep {rr[2]:.5f}, margin {mpos:.2e})"); return True
    if nest >= maxnest or (nest >= 1 and r_self > R_NEST):
        bump('fail'); return False
    # nest: full scans of the odd tiles, smallest hard set first
    best = None
    for nm in pref:
        iv, nlp, mpos = scan(tiles[nm], (nest, nm), discs, tau, N=NFULL, early=False)
        bump('lps', nlp)
        hl = sum(b - a for a, b, _ in iv)
        if best is None or hl < best[2]: best = (nm, iv, hl)
    nm, hm, hl = best
    log(f"{tag} nest on {nm}: hard {hl:.4f} " + ", ".join(f"[{a:.4f},{b:.4f}]" for a, b, _ in hm[:4]) + f" (rep {rr[2]:.5f})")
    tl = tiles[nm]
    for (a, b, _) in hm:
        stack = [(a, b)]
        while stack:
            q0, q1 = stack.pop()
            D, mu = NP.hard_disc(tl, q0, q1, w0, tau)
            if D['r'] <= RMAX:
                bump('sub')
                if solve(discs + [D], tau, tiles, nest + 1, maxnest, tag + f"/{nm}[{q0:.6f},{q1:.6f}]r{D['r']:.1e}", log, r_self=D['r']):
                    continue
            if q1 - q0 < minarc:
                log(f"{tag}/{nm}[{q0:.8f},{q1:.8f}] FAIL at min width"); return False
            m = (q0 + q1)/2; stack += [(q0, m), (m, q1)]
    return True
