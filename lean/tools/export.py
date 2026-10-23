"""Export a verify.py certificate (CERTDIR with meta.json + jobs/*.jsonl.gz) to Lean data.

1. Flatten the job logs into ONE global DFS record stream: every "S" (delegated) record is replaced
   by the records of the job whose root path is that node's path (recursively).
2. Re-check the flattened stream exactly with the semantics of the Lean checker
   (Autocorr/Cert/Checker.lean), using verify.py's own Spec (rows, propagation) as the reference:
   regions are recomputed by propagation, every leaf bound is evaluated exactly and must be >= lam.
3. Cut the stream into segments (consecutive records) and record the DFS stack (list of boxes) at
   every cut. Encode every segment as a string of base-32 varints in the base64 alphabet.

Encoding (all integers zigzag, little-endian base 32; alphabet A-Z a-z 0-9 + / ; values >= 32 mean
"more digits follow"):
  segment := version(=1) n lam_num lam_den stack records stack
  stack   := count box*          box := L_0..L_{nB-1} U_0..U_{nB-1}  (numerators over 2^30)
  records := count rec*
  rec     := 0 b s_num                      split at s = s_num / 2^30
           | 1 m (key num e)*m               leaf with duals y = num / 2^e
           | 2 m (key num e)*m               Farkas
  key     := 0 c1 c2 | 1 c | 2 c | 3 b | 4 d e s | 5 i | 6 | 7 d e q
"""
import sys, os, json, gzip, glob, time, argparse
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import checker_path
checker_path.add_checker_path()
import verify  # reference semantics (read-only)

SB = 30
ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
KIND = {"win": 0, "P": 1, "G": 2, "tree": 3, "ZA": 4, "rlt": 5, "sym": 6, "mc": 7}


def enc_int(v, out):
    z = 2 * v if v >= 0 else -2 * v - 1
    while True:
        d = z & 31
        z >>= 5
        if z:
            out.append(ALPHA[32 + d])
        else:
            out.append(ALPHA[d])
            return


def scaled(x, bits):
    v = x * (1 << bits)
    if v.denominator != 1:
        raise ValueError(f"{x} is not a multiple of 2^-{bits}")
    return v.numerator


def load_jobs(certdir):
    files = sorted(glob.glob(os.path.join(certdir, "jobs", "*.jsonl.gz")))
    by_root = {}
    for f in files:
        with gzip.open(f, "rt") as fh:
            h = json.loads(fh.readline())
        key = tuple((int(b), str(Fr(s)), int(side)) for b, s, side in h["path"])
        if key in by_root:
            raise AssertionError("two jobs with the same root path")
        by_root[key] = f
    return by_root


def read_records(f):
    with gzip.open(f, "rt") as fh:
        h = json.loads(fh.readline())
        return h, [json.loads(line) for line in fh]


def flatten(spec, by_root, lam, rowkeys, sink, check=True):
    """Global DFS. Calls sink(kind, payload, stack_before) for every non-S record, in stream order.
    Mirrors verify.verify_job; S records are expanded in place. Returns stats."""
    root = spec.root_region()
    stack = [(root, ())]
    stats = {"leaves": 0, "internal": 0, "empty": 0, "farkas": 0, "jobs": 0, "minlb": None}
    used_jobs = set()
    # iterator stack over job record lists
    todo = [iter(read_records(by_root[()])[1])]
    used_jobs.add(())
    stats["jobs"] += 1
    while todo:
        try:
            rec = next(todo[-1])
        except StopIteration:
            todo.pop()
            continue
        kind = rec[0]
        if kind == "S":
            reg, path = stack[-1]
            if path not in by_root:
                raise AssertionError(f"delegated path without job: {path}")
            if path in used_jobs:
                raise AssertionError("job used twice")
            used_jobs.add(path)
            stats["jobs"] += 1
            h, recs = read_records(by_root[path])
            todo.append(iter(recs))
            continue
        if not stack:
            raise AssertionError("record with empty stack")
        reg, path = stack.pop()
        if kind == "I":
            b, s = rec[1], Fr(rec[2])
            stats["internal"] += 1
            sink("I", (b, s), stack, reg)
            for side in (0, 1):
                cr = spec.child(reg, b, s, side)
                if cr is None:
                    stats["empty"] += 1
                else:
                    stack.append((cr, path + ((b, str(s), side),)))
        elif kind == "L":
            if check:
                lb = verify.leaf_bound(spec, reg, rowkeys, None, rec[2], rec[3])
                if lb < lam:
                    raise AssertionError(f"leaf bound {float(lb)} < lam")
                stats["minlb"] = lb if stats["minlb"] is None else min(stats["minlb"], lb)
            stats["leaves"] += 1
            sink("L", (rec[2], rec[3]), stack, reg)
        elif kind == "F":
            if check and not verify.farkas_ok(spec, reg, rowkeys, rec[1], rec[2]):
                raise AssertionError("Farkas fails")
            stats["farkas"] += 1
            sink("F", (rec[1], rec[2]), stack, reg)
        else:
            raise AssertionError(f"unknown record {kind}")
    if stack:
        raise AssertionError("nodes left")
    if used_jobs != set(by_root):
        raise AssertionError(f"{len(set(by_root) - used_jobs)} jobs unreachable")
    return stats


def enc_box(reg, out):
    L, U = reg
    for x in L:
        enc_int(scaled(x, SB), out)
    for x in U:
        enc_int(scaled(x, SB), out)


def enc_stack(stack_regs, out):
    enc_int(len(stack_regs), out)
    for reg in stack_regs:
        enc_box(reg, out)


def enc_duals(rowkeys, idx, vals, out):
    """Each dual y = num / 2^e exactly (IEEE doubles are dyadic)."""
    ys = [(rowkeys[k], Fr(v)) for k, v in zip(idx, vals) if Fr(v) != 0]
    enc_int(len(ys), out)
    for key, y in ys:
        d = y.denominator
        e = d.bit_length() - 1
        if (1 << e) != d:
            raise ValueError("non-dyadic dual")
        enc_int(KIND[key[0]], out)
        for a in key[1:]:
            enc_int(a, out)
        enc_int(y.numerator, out)
        enc_int(e, out)


def lean_stack(py_stack):
    """verify.py's stack has its top at the END; the Lean stack (a List) has its top at the HEAD."""
    return [reg for reg, _ in reversed(py_stack)]


class SegWriter:
    """Collects records into segments of about `seg_leaves` leaves; cuts only after leaf records.
    Each segment stores the Lean stack before its first record and after its last record."""

    def __init__(self, rowkeys, seg_leaves):
        self.rowkeys, self.seg_leaves = rowkeys, seg_leaves
        self.segs = []          # list of (stack_in, [encoded records], nleaves, stack_out)
        self.cur = None

    def sink(self, kind, payload, stack, reg):
        # called after the pop: the stack before this record is stack + [reg]
        if self.cur is None:
            self.cur = [lean_stack(stack + [(reg, None)]), [], 0]
        out = []
        if kind == "I":
            b, s = payload
            enc_int(0, out); enc_int(b, out); enc_int(scaled(s, SB), out)
        else:
            enc_int(1 if kind == "L" else 2, out)
            enc_duals(self.rowkeys, payload[0], payload[1], out)
            self.cur[2] += 1
        self.cur[1].append("".join(out))
        if kind != "I" and self.cur[2] >= self.seg_leaves:
            # leaf/Farkas records push nothing: the stack after this record is `stack`
            self.segs.append((self.cur[0], self.cur[1], self.cur[2], lean_stack(stack)))
            self.cur = None

    def finish(self):
        if self.cur is not None:
            self.segs.append((self.cur[0], self.cur[1], self.cur[2], []))
            self.cur = None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir")
    ap.add_argument("outdir")
    ap.add_argument("--seg-leaves", type=int, default=10 ** 9)
    ap.add_argument("--no-check", action="store_true")
    args = ap.parse_args()
    meta = json.load(open(os.path.join(args.certdir, "meta.json")))
    n = meta["n"]; lam = Fr(meta["lam"])
    spec = verify.Spec(n)
    rowkeys = [spec.validate_key(tuple(k)) for k in meta["rowkeys"]]
    by_root = load_jobs(args.certdir)
    t0 = time.time()
    W = SegWriter(rowkeys, args.seg_leaves)
    stats = flatten(spec, by_root, lam, rowkeys, W.sink, check=not args.no_check)
    W.finish()
    print(f"flattened+checked in {time.time()-t0:.1f}s: {stats}; segments={len(W.segs)}", flush=True)
    os.makedirs(args.outdir, exist_ok=True)
    header = []
    enc_int(1, header); enc_int(n, header); enc_int(lam.numerator, header); enc_int(lam.denominator, header)
    header = "".join(header)
    for k, (sin, recs, nl, sout) in enumerate(W.segs):
        out = [header]
        o = []; enc_stack(sin, o); out.append("".join(o))
        o = []; enc_int(len(recs), o); out.append("".join(o))
        out.extend(recs)
        o = []; enc_stack(sout, o); out.append("".join(o))
        with open(os.path.join(args.outdir, f"seg{k:06d}.txt"), "w") as fh:
            fh.write("".join(out))
    json.dump({"n": n, "lam": str(lam), "segments": len(W.segs),
               "stats": {k: (str(v) if isinstance(v, Fr) else v) for k, v in stats.items()}},
              open(os.path.join(args.outdir, "export.json"), "w"))


if __name__ == "__main__":
    main()
