"""Same-tree check for two copies of a B&B certificate (e.g. a tree-only certificate and the filled certificate written
by verify_tree_dump.py, or D-record job logs and their tree-only conversion).

usage: idcheck_tree.py DIR_A DIR_B [--workers W] [--strict-names]
DIR_A, DIR_B: certificate directories (job logs in DIR/jobs/*.jsonl.gz) or plain directories of job logs.
For every job log name in DIR_A, the file of the same name in DIR_B must exist (and, with --strict-names, no extra
names in DIR_B).  Per job:
  * the header lines must be equal as JSON objects, except the "stats" field (writer bookkeeping);
  * K records (cut tables) are skipped on both sides;
  * the remaining records must pair up one to one: a LEAF record (U, T, L, C, D, E) on one side must face a leaf record
    (of any of these kinds) on the other side; every other record (I, S, F, ...) must be identical (JSON equality,
    so split values compare as the same rational strings).
Exit status 0 iff every job matches.  Prints totals and the first mismatches.
"""
import sys, os, json, gzip, glob, argparse
from multiprocessing import get_context

LEAF = {"U", "T", "L", "C", "D", "E"}


def jobfiles(d):
    j = os.path.join(d, "jobs")
    base = j if os.path.isdir(j) else d
    return base, sorted(os.path.basename(f) for f in glob.glob(os.path.join(base, "*.jsonl.gz")))


def records(fn):
    with gzip.open(fn, "rt") as fh:
        header = json.loads(fh.readline())
        for line in fh:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if isinstance(r, list) and r and r[0] == "K":
                continue
            yield header, r


def check_job(args):
    a, b, name = args
    fa, fb = os.path.join(a, name), os.path.join(b, name)
    if not os.path.exists(fb):
        return name, "missing in B", 0, 0
    with gzip.open(fa, "rt") as fh:
        ha = json.loads(fh.readline())
    with gzip.open(fb, "rt") as fh:
        hb = json.loads(fh.readline())
    ha = {k: v for k, v in ha.items() if k != "stats"}; hb = {k: v for k, v in hb.items() if k != "stats"}
    if ha != hb:
        return name, "header differs", 0, 0
    ra = (r for _, r in records(fa)); rb = (r for _, r in records(fb))
    n = 0; leaves = 0
    while True:
        x = next(ra, None); y = next(rb, None)
        if x is None and y is None:
            return name, None, n, leaves
        if x is None or y is None:
            return name, f"record count differs after {n} records", n, leaves
        n += 1
        if x[0] in LEAF or y[0] in LEAF:
            if not (x[0] in LEAF and y[0] in LEAF):
                return name, f"record {n}: leaf {x[0]} vs {y[0]}", n, leaves
            leaves += 1
        elif x != y:
            return name, f"record {n}: {json.dumps(x)[:80]} vs {json.dumps(y)[:80]}", n, leaves


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("a"); ap.add_argument("b")
    ap.add_argument("--workers", type=int, default=1); ap.add_argument("--strict-names", action="store_true")
    o = ap.parse_args()
    a, na = jobfiles(o.a); b, nb = jobfiles(o.b)
    bad = []
    if o.strict_names:
        extra = sorted(set(nb) - set(na))
        if extra:
            bad.append(("(B only)", f"{len(extra)} job logs only in B, e.g. {extra[0]}"))
    tasks = [(a, b, x) for x in na]
    if o.workers > 1:
        with get_context("fork").Pool(o.workers) as pool:
            res = pool.map(check_job, tasks, chunksize=64)
    else:
        res = [check_job(t) for t in tasks]
    nrec = sum(r[2] for r in res); nleaf = sum(r[3] for r in res)
    bad += [(r[0], r[1]) for r in res if r[1] is not None]
    print(f"jobs {len(na)} (B: {len(nb)}); records compared {nrec}; leaf pairs {nleaf}; mismatching jobs {len(bad)}")
    for x in bad[:20]:
        print("MISMATCH", x[0], x[1])
    if bad:
        sys.exit(1)
    print("SAME TREE")


if __name__ == "__main__":
    main()
