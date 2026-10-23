# phase-B queue worker: keeps NPROC tasks in flight, claiming them one at a time from the server; results appended to OUT.
# usage: qworker.py SERVER_URL VMNAME CFG NPROC OUT
import sys, os, json, time, urllib.request
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_nested3 as G3
from multiprocessing import Pool
url, vm, cfgp, nproc, out = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
def claim():
    for attempt in range(20):
        try:
            with urllib.request.urlopen(f"{url}/claim?vm={vm}", timeout=30) as r:
                if r.status == 204: return None
                return json.loads(r.read().decode())
        except Exception as e:
            time.sleep(5 + 5*attempt)
    return None
if __name__ == "__main__":
    cfg = json.load(open(cfgp)); g = G3.setup(cfg)
    print("module shas", json.dumps(G3.module_shas()), flush=True)
    import threading
    J = open(out, "a"); t0 = time.time(); st = {"n": 0, "inflight": 0}; empty = False; lk = threading.Lock()
    def cb(r):
        with lk:
            J.write(json.dumps(r) + "\n"); J.flush(); st["inflight"] -= 1; st["n"] += 1; n = st["n"]
        if n % 50 == 0 or not r["ok"]:
            print(f"[{time.time()-t0:7.1f}s] {n} done, last k={r['k']} {'FAIL' if not r['ok'] else 'ok'} {r['stats']}", flush=True)
    def ecb(e):
        with lk:
            st["inflight"] -= 1
        print(f"[{time.time()-t0:7.1f}s] TASK EXCEPTION {type(e).__name__}: {e}", flush=True)
    with Pool(nproc, initializer=G3.init, initargs=(g,)) as pool:
        open(out + ".pid", "w").write(f"{os.getpid()}\n")
        while True:
            while st["inflight"] < nproc and not empty:
                t = claim()
                if t is None: empty = True; break
                with lk:
                    st["inflight"] += 1
                pool.apply_async(G3.phase_B, (t,), callback=cb, error_callback=ecb)
            if empty and st["inflight"] == 0: break
            time.sleep(1)
    print(f"[{time.time()-t0:7.1f}s] QUEUE EMPTY, {st['n']} tasks done", flush=True)
