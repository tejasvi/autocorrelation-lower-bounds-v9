# Streaming coverage/header check over the SUBSET certificates of one assembly (the full certificate is their concatenation):
# every subset must carry the same header, the header must pass the same conditions as check_nested.main(), and the union of
# all arcs' [s0, s1] must tile [0, 1] exactly (sorted, contiguous, no overlaps or duplicates).  Per-arc verdicts come from the
# --subset runs of the checker of record.  Loads one subset at a time.  usage: coverage_subsets2.py 'SUBSET_GLOB' EXPECTED_ARCS SHA256SUMS EXPECTED_FILES
# Version 2 (2026-10-23): refuses python -O (every check is an assert), requires exactly EXPECTED_FILES subset files, and checks
# each file's sha256 against the SHA256SUMS manifest (by file name) before reading it.
import sys, json, gzip, glob, hashlib
from fractions import Fraction
if not __debug__:
    sys.exit("coverage_subsets2: refusing to run with python -O")
files = sorted(glob.glob(sys.argv[1])); assert files, "no subset files"
expect = int(sys.argv[2])
sums = {}
for l in open(sys.argv[3]):
    if l.strip(): h, n = l.split(None, 1); sums[n.strip().lstrip("*").split("/")[-1]] = h
if len(files) != int(sys.argv[4]):
    sys.exit(f"coverage_subsets2: {len(files)} subset files, expected {sys.argv[4]}")
for fn in files:
    h = hashlib.sha256()
    with open(fn, "rb") as fh:
        for b in iter(lambda: fh.read(1 << 24), b""): h.update(b)
    if sums.get(fn.split("/")[-1]) != h.hexdigest():
        sys.exit(f"coverage_subsets2: sha256 of {fn} does not match the manifest")
print(f"manifest: {len(files)} subset files, all sha256 match", flush=True)
head0 = None; iv = []; types = {}
for fn in files:
    C = json.load(gzip.open(fn, "rt")) if fn.endswith(".gz") else json.load(open(fn))
    head = {k: C[k] for k in C if k != "arcs"}
    if head0 is None:
        head0 = head
        assert C["variant"] == "Cp"
        tau = Fraction(C["tau"]); assert 0 < tau < 1
        c, a, b = (Fraction(x) for x in C["T1"]); assert a > 0 and b > 0
        lo, hi = c - a, c + a
        ints = [n for n in range(int(lo) - 2, int(hi) + 3) if n != 0 and lo < n < hi]
        assert len(ints) == 1, "T1 must enclose exactly one zero of S"
        assert not (lo.denominator == 1 and lo != 0) and not (hi.denominator == 1 and hi != 0), "S vanishes on T1"
        for key, tl in C["tiles"].items():
            cr, ci, ta, tb = (Fraction(x) for x in tl); assert ta > 0 and tb > 0
        iv_eps = Fraction(C.get("iv_eps", "1/1000000000")); assert 0 <= iv_eps <= Fraction(1, 1000), "iv_eps out of range"
    else:
        assert head == head0, f"header differs in {fn}"
    for arc in C["arcs"]:
        assert arc["type"] in ("E", "H", "H3", "N")
        s0, s1 = Fraction(arc["s0"]), Fraction(arc["s1"]); assert s0 < s1
        iv.append((s0, s1)); types[arc["type"]] = types.get(arc["type"], 0) + 1
    del C
iv.sort()
assert iv[0][0] == 0 and iv[-1][1] == 1, "arcs must cover [0,1]"
for i in range(len(iv) - 1):
    assert iv[i][1] == iv[i + 1][0], f"arcs not contiguous at {iv[i]} / {iv[i + 1]}"
assert len(iv) == expect, f"{len(iv)} arcs, expected {expect}"
print(f"COVERAGE OK over {len(files)} subsets: tau = {head0['tau']}, {len(iv)} arcs tile [0,1] {types}; header sha "
      f"{hashlib.sha256(json.dumps(head0, sort_keys=True).encode()).hexdigest()[:16]}")
