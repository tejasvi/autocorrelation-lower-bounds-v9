"""Production entry point for the optimized solver (frozen copies src/bnbopt.py, src/implied.py of opt/, 2026-10-19).

  bnbcert2.py init CERTDIR n lam [--depth D] [--opts JSON]
  bnbcert2.py work CERTDIR [--workers W] [--max-nodes M]
  bnbcert2.py status CERTDIR | recover CERTDIR
With opts {"psd": "m3", "compress": true, "cut_table": true} it writes the extended format checked by src/verify_cmp.py.
"""
import sys, os, glob, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bnbopt as B


def cmd_recover(certdir):
    """Move jobs left in running/ by an interrupted run back to todo/ (only when no worker is alive)."""
    for f in glob.glob(os.path.join(certdir, "running", "*.json")):
        jid = os.path.basename(f)[:-5]
        if not os.path.exists(os.path.join(certdir, "jobs", jid + ".jsonl.gz")):
            os.rename(f, os.path.join(certdir, "todo", os.path.basename(f)))
        else:
            os.rename(f, os.path.join(certdir, "done", os.path.basename(f)))


def cmd_status(certdir):
    c = lambda d: len(glob.glob(os.path.join(certdir, d, "*.json")))
    print(f"todo={c('todo')} running={c('running')} done={c('done')}")


if __name__ == "__main__":
    import argparse
    cmd = sys.argv[1]
    if cmd == "init":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir"); ap.add_argument("n", type=int)
        ap.add_argument("lam"); ap.add_argument("--depth", type=int, default=10); ap.add_argument("--opts", default="{}")
        a = ap.parse_args(); B.cmd_init(a.certdir, a.n, a.lam, a.depth, json.loads(a.opts))
    elif cmd == "work":
        ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("certdir")
        ap.add_argument("--workers", type=int, default=1); ap.add_argument("--max-nodes", type=int, default=20000)
        a = ap.parse_args(); B.cmd_work(a.certdir, a.workers, a.max_nodes)
    elif cmd == "recover":
        cmd_recover(sys.argv[2])
    elif cmd == "status":
        cmd_status(sys.argv[2])
    else:
        sys.exit("unknown command")
