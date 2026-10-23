# minimal task-claim server for phase B (runs on one fleet VM): GET /claim -> one task JSON line (204 when empty);
# GET /stat -> counts.  Tasks = all tasks minus the done keys given at start.  Claims are logged (append) for recovery.
# usage: qserver.py PORT TASKS_GLOB DONE_KEYS.txt CLAIMLOG
import sys, os, json, glob, random, threading
from fractions import Fraction
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
port = int(sys.argv[1]); tg = sys.argv[2]; donef = sys.argv[3]; logf = sys.argv[4]
done = set(l.strip() for l in open(donef) if l.strip())
tasks = []
for fn in sorted(glob.glob(tg)):
    for l in open(fn):
        t = json.loads(l); key = json.dumps([t["k"], t["q0"], t["q1"]])
        if key not in done: tasks.append(l.strip())
random.Random(777).shuffle(tasks)
claimed = set()
try:
    for l in open(logf): claimed.add(l.split("\t", 1)[1].strip())
except FileNotFoundError:
    pass
tasks = [t for t in tasks if t not in claimed]          # originals claimed earlier (done or in flight)
# priority (pop() takes from the end): long tasks first = band pieces of T3d (crossings near/after the lower 3/4 pass:
# q in [0.78, 0.94] for 'up' tiles, the mirror [0.06, 0.22] for 'dn' tiles), then the rest, in shuffled order
def band(line):
    t = json.loads(line); q = (float(Fraction(t["q0"])) + float(Fraction(t["q1"])))/2
    if not t["tile"].startswith("T3d"): return 0
    return 1 if ((t["tile"].endswith("up") and 0.78 <= q <= 0.94) or (t["tile"].endswith("dn") and 0.06 <= q <= 0.22)) else 0
# optional: split the remaining band tasks into SPLIT equal q-pieces (each piece is an independent task; the assembler accepts
# any exact tiling of an original task piece by result pieces)
SPLIT = int(os.environ.get("SPLIT", "1"))
if SPLIT > 1:
    out = []
    for line in tasks:
        if band(line):
            t = json.loads(line); q0, q1 = Fraction(t["q0"]), Fraction(t["q1"])
            for i in range(SPLIT):
                t2 = dict(t); t2["q0"] = str(q0 + (q1 - q0)*i/SPLIT); t2["q1"] = str(q0 + (q1 - q0)*(i + 1)/SPLIT)
                out.append(json.dumps(t2))
        else:
            out.append(line)
    tasks = [t for t in out if t not in claimed]        # pieces claimed earlier
tasks.sort(key=band)
lock = threading.Lock(); LOG = open(logf, "a")
print(f"queue: {len(tasks)} tasks ({len(done)} done keys, {len(claimed)} previously claimed)", flush=True)
class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def do_GET(self):
        if self.path.startswith("/claim"):
            with lock:
                t = tasks.pop() if tasks else None
                if t is not None:
                    vm = self.path.split("vm=")[-1] if "vm=" in self.path else "?"
                    LOG.write(f"{vm}\t{t}\n"); LOG.flush()
            if t is None:
                self.send_response(204); self.end_headers(); return
            b = t.encode()
            self.send_response(200); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
        elif self.path.startswith("/stat"):
            b = json.dumps({"remaining": len(tasks)}).encode()
            self.send_response(200); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b)
        else:
            self.send_response(404); self.end_headers()
ThreadingHTTPServer(("0.0.0.0", port), H).serve_forever()
