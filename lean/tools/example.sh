#!/bin/bash
# Small worked examples (a few minutes after `lake exe cache get` and the library build):
#   KT8: kernel-only proof of V_8 >= 59/50 from examples/cert_test8 (17 jobs, 142 leaves);
#   T8 : native_decide proof of the same;
#   X12: native_decide proof of V_12 >= 49/40 from examples/t12m3 (format 2: square cuts, compressed leaves).
# Outputs (logs, #print axioms) go to examples/out/<PKG>/.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
W=${1:-8}
cd "$ROOT"
OUTDIR=$ROOT/examples/out/KT8 GROUP_LEAVES=40 SEG_LEAVES=4 tools/run_m4.sh examples/cert_test8 KT8 8 59 50 "$W"
OUTDIR=$ROOT/examples/out/T8 GROUP_LEAVES=40 tools/run_m3.sh examples/cert_test8 T8 8 59 50 "$W"
OUTDIR=$ROOT/examples/out/X12 GROUP_LEAVES=0 tools/run_m3x.sh examples/t12m3 X12 12 49 40 "$W"
for P in KT8 T8 X12; do echo "== $P"; grep "depends on axioms" -A3 "examples/out/$P/axioms.txt" | head -4; done
