"""Locate the Python certificate checkers (verify.py, verify_cmp.py) whose Spec the exporters reuse.

Search order: $AUTOCORR_CHECKER, ../../checker (layout of the public repository: lean/tools -> checker/),
../../src (development layout)."""
import os, sys


def add_checker_path():
    here = os.path.dirname(os.path.abspath(__file__))
    for c in (os.environ.get("AUTOCORR_CHECKER"), os.path.join(here, "..", "..", "checker"),
              os.path.join(here, "..", "..", "src")):
        if c and os.path.exists(os.path.join(c, "verify.py")):
            c = os.path.abspath(c)
            if c not in sys.path:
                sys.path.insert(0, c)
            return c
    raise SystemExit("cannot find verify.py: set AUTOCORR_CHECKER to the directory holding verify.py / verify_cmp.py")
