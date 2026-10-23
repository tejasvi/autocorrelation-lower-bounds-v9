"""Tree-only copy of a D-record certificate written by bnbtree.py with {"tree_only": false, "d_compat": true}.

usage: d2tree.py SRC_CERTDIR DST_CERTDIR [--workers W]
Per job log: the header line is copied byte for byte; every K record is dropped; every D record becomes ["U"]; every
other record (I, S, U, L, F, ...) is copied unchanged.  meta.json is copied.  (Unlike to_tree.py --nocuts, thin-margin L
leaves keep their explicit duals, as in a certificate written directly in tree-only mode.)  The result has the same
tree (check with idcheck_tree.py) and is a tree-only certificate in the sense of TREE_FORMAT.md.
"""
import sys, os, json, gzip, glob, shutil, argparse
from multiprocessing import get_context


def convert(args):
    f, dst = args
    out = os.path.join(dst, "jobs", os.path.basename(f))
    nd = nk = 0
    with gzip.open(f, "rt") as fh, gzip.open(out + ".tmp", "wt", compresslevel=9) as oh:
        oh.write(fh.readline())
        for line in fh:
            r = json.loads(line)
            k = r[0]
            if k == "K":
                nk += 1
                continue
            if k == "D":
                nd += 1
                oh.write('["U"]\n')
            else:
                oh.write(line if line.endswith("\n") else line + "\n")
    os.replace(out + ".tmp", out)
    return nd, nk, os.path.getsize(f), os.path.getsize(out)


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("src"); ap.add_argument("dst"); ap.add_argument("--workers", type=int, default=1)
    a = ap.parse_args()
    os.makedirs(os.path.join(a.dst, "jobs"), exist_ok=True)
    shutil.copy(os.path.join(a.src, "meta.json"), os.path.join(a.dst, "meta.json"))
    files = sorted(glob.glob(os.path.join(a.src, "jobs", "*.jsonl.gz")))
    tasks = [(f, a.dst) for f in files]
    if a.workers > 1:
        with get_context("fork").Pool(a.workers) as pool:
            res = pool.map(convert, tasks, chunksize=64)
    else:
        res = [convert(t) for t in tasks]
    nd = sum(r[0] for r in res); nk = sum(r[1] for r in res); b0 = sum(r[2] for r in res); b1 = sum(r[3] for r in res)
    print(f"jobs {len(files)}; D -> U {nd}; K dropped {nk}; bytes {b0} -> {b1} ({b0 / max(1, b1):.1f}x)")


if __name__ == "__main__":
    main()
