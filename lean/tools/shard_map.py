"""Split a job tree into build shards (complete delegation subtrees) and an assembly shard (the jobs above them).

usage: shard_map.py CERTDIR NSHARDS OUT.json [--workers W] [--top-frac F]
Reads only the header line of every job file (its root path).  The parent of a job is the job whose root path is
the longest proper prefix of its own; subtree weights are sums of job file sizes.  The tree is cut from the root:
the heaviest frontier subtree is opened (its root moves to the assembly shard) until no frontier subtree weighs more
than F * total / NSHARDS (default F = 0.5); the frontier subtrees are then packed greedily into NSHARDS shards.
OUT.json: {"assembly": [job ids], "shards": [[subtree root ids], ...], "jobs": {job id: shard (-1 = assembly)},
           "external": {enc_path of a subtree root: job id}}  (the last one is the assembly's --external map).
"""
import sys, os, json, gzip, glob, argparse, heapq
from fractions import Fraction as Fr
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def head(f):
    with gzip.open(f, "rt") as fh:
        h = json.loads(fh.readline())
    b = os.path.basename(f)[:-len(".jsonl.gz")]
    return b, tuple((int(x[0]), str(Fr(x[1])), int(x[2])) for x in h["path"]), os.path.getsize(f)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("nshards", type=int)
    ap.add_argument("out")
    ap.add_argument("--workers", type=int, default=16)
    ap.add_argument("--top-frac", type=float, default=0.5)
    a = ap.parse_args()
    files = sorted(glob.glob(os.path.join(a.certdir, "jobs", "*.jsonl.gz")))
    with Pool(a.workers) as p:
        hs = p.map(head, files, chunksize=256)
    out = plan(hs, a.nshards, a.top_frac)
    json.dump(out, open(a.out, "w"))
    loads = out["loads"]
    print(f"{len(hs)} jobs, total {out['total_bytes']/1e9:.2f} GB; assembly {len(out['assembly'])} jobs "
          f"({out['assembly_bytes']/1e6:.1f} MB); shard loads GB min {min(loads)/1e9:.2f} max {max(loads)/1e9:.2f}")


def plan(hs, nshards, top_frac=0.5):
    """hs: [(job id, root path key, size)] -> the shard plan (see the module docstring)."""
    byp = {}
    for b, path, sz in hs:
        if path in byp:
            raise ValueError("duplicate root path")
        byp[path] = (b, sz)
    if () not in byp:
        raise ValueError("no root job")
    kids = {b: [] for b, _, _ in hs}
    parent = {}
    for b, path, sz in hs:
        if path == ():
            continue
        for L in range(len(path) - 1, -1, -1):
            q = path[:L]
            if q in byp:
                parent[b] = byp[q][0]; kids[byp[q][0]].append(b); break
    root = byp[()][0]
    size = {b: sz for b, _, sz in hs}
    pathof = {b: path for b, path, _ in hs}
    # subtree weights (iterative post-order)
    w = {}
    order = []; stack = [(root, False)]
    while stack:
        b, done = stack.pop()
        if done:
            order.append(b); continue
        stack.append((b, True))
        stack.extend((c, False) for c in kids[b])
    if len(order) != len(hs):
        raise ValueError("jobs not reachable from the root (orphans)")
    for b in order:
        w[b] = size[b] + sum(w[c] for c in kids[b])
    total = w[root]
    cap = top_frac * total / nshards
    assembly = []
    frontier = [(-w[root], root)]
    while frontier and -frontier[0][0] > cap:
        _, b = heapq.heappop(frontier)
        assembly.append(b)
        for c in kids[b]:
            heapq.heappush(frontier, (-w[c], c))
    subroots = sorted((b for _, b in frontier), key=lambda b: -w[b])
    bins = [(0, i) for i in range(nshards)]
    heapq.heapify(bins)
    shards = [[] for _ in range(nshards)]
    for b in subroots:
        load, i = heapq.heappop(bins)
        shards[i].append(b)
        heapq.heappush(bins, (load + w[b], i))
    jobs = {b: -1 for b in assembly}
    for i, sr in enumerate(shards):
        for r in sr:
            st = [r]
            while st:
                b = st.pop(); jobs[b] = i; st.extend(kids[b])
    if len(jobs) != len(hs):
        raise ValueError("shard assignment incomplete")
    import export_jobsx as X        # enc_path, for the assembly's --external map
    ext = {X.enc_path([(p[0], Fr(p[1]), p[2]) for p in pathof[r]]): r for sr in shards for r in sr}
    loads = [sum(w[r] for r in sr) for sr in shards]
    return {"assembly": assembly, "shards": shards, "jobs": jobs, "external": ext,
            "loads": loads, "assembly_bytes": sum(size[b] for b in assembly), "total_bytes": total}


if __name__ == "__main__":
    main()
