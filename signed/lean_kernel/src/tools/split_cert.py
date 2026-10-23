#!/usr/bin/env python3
"""Split a three-level certificate into glob.json (variant, tau, T1, tiles, number of arcs) and arcs/NNNN.json
(arcs sorted by s0).  Read-only on the certificate; records the sha256 of the input in glob.json."""
import gzip, hashlib, json, os, sys
from fractions import Fraction as F
cert, out = sys.argv[1], sys.argv[2]
h = hashlib.sha256(open(cert, "rb").read()).hexdigest()
C = json.load(gzip.open(cert, "rt") if cert.endswith(".gz") else open(cert))
arcs = sorted(C["arcs"], key=lambda x: F(x["s0"]))
os.makedirs(os.path.join(out, "arcs"), exist_ok=True)
for i, a in enumerate(arcs):
    with open(os.path.join(out, "arcs", "%04d.json" % i), "w") as fh:
        json.dump(a, fh, separators=(",", ":"))
g = {k: C[k] for k in ("variant", "tau", "T1", "tiles")}
g["n_arcs"] = len(arcs)
g["cert_sha256"] = h
json.dump(g, open(os.path.join(out, "glob.json"), "w"), indent=1)
print("arcs", len(arcs), "sha256", h)
