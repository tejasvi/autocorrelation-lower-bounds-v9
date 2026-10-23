# Runner for the checker of record check_nested vC (full sha256 below, checked explicitly, not by assert).  It
#  (0) refuses to run under python -O;
#  (1) forces the 'fork' start method (Python 3.14 defaults to 'forkserver', which loses the module-global certificate);
#  (2) calls gc.freeze() right after the certificate is loaded (forked workers then do not copy the parent heap);
#  (3) exits non-zero if the checker exits non-zero, and with --subset also unless the checker printed exactly one line
#      "SUBSET: n of n arcs pass" with equal counts.
# Same arguments and output as check_nested.py.  Linux only.  usage: python -I check_run2.py CHECKER.py CERT [NPROC] [--subset] [--deep]
import sys, io, re, json, gc, hashlib, importlib.util, multiprocessing
if not __debug__:
    sys.exit("check_run2: refusing to run with python -O")
SHA = "593964e8336bfc6606e684275d556b39c784a79690ef2084ab82b9c61556283e"
chk = sys.argv[1]
if hashlib.sha256(open(chk, "rb").read()).hexdigest() != SHA:
    sys.exit("check_run2: not check_nested vC (sha256 mismatch)")
multiprocessing.set_start_method("fork", force=True)
_load = json.load
def _load_then_freeze(*a, **k):
    r = _load(*a, **k); gc.freeze(); return r
json.load = _load_then_freeze
class Tee(io.TextIOBase):
    def __init__(self, s): self.s = s; self.buf = []
    def write(self, x): self.buf.append(x); return self.s.write(x)
    def flush(self): self.s.flush()
spec = importlib.util.spec_from_file_location("check_nested", chk)
CN = importlib.util.module_from_spec(spec); sys.modules["check_nested"] = CN; spec.loader.exec_module(CN)
args = [a for a in sys.argv[2:] if a not in ("--subset", "--deep")]
subset = "--subset" in sys.argv
tee = Tee(sys.stdout); sys.stdout = tee
try:
    CN.main(args[0], int(args[1]) if len(args) > 1 else 8, subset=subset, deep="--deep" in sys.argv)
except SystemExit as e:
    sys.stdout = tee.s
    if e.code not in (None, 0):
        sys.exit(e.code if isinstance(e.code, int) else 1)
sys.stdout = tee.s
if subset:
    m = re.findall(r"^SUBSET: (\d+) of (\d+) arcs pass$", "".join(tee.buf), re.M)
    if len(m) != 1 or m[0][0] != m[0][1]:
        sys.exit("check_run2: no single 'SUBSET: n of n arcs pass' line")
