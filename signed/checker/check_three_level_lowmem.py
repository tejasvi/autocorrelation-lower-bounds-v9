#!/usr/bin/env python3
"""Low-memory runner for check_three_level.py: it calls that checker's main() unchanged, but makes its worker pool use the
forkserver start method, so the workers do not inherit the parsed certificate. (With fork, every worker's copy-on-write image
of the parsed certificate is gradually copied; for a 1.3 GB-gz certificate the parent holds about 19 GB, and a few hundred
such workers exhaust the memory of a large server.) The checks performed are exactly those of check_three_level.py.
Usage: python3 -I check_three_level_lowmem.py cert.json.gz [nproc]"""
import os, sys, hashlib, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_three_level as chk

if __name__ == "__main__":
    print("checker", chk.__file__, "sha256", hashlib.sha256(open(chk.__file__, "rb").read()).hexdigest(), flush=True)
    chk.Pool = mp.get_context("forkserver").Pool
    chk.main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 8)
