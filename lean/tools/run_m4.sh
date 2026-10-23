#!/bin/bash
# Kernel-only proof (decide +kernel, no native code) of V_N >= A/B from a format-1 certificate.
# usage: tools/run_m4.sh CERTDIR PKG N A B [WORKERS]
# env: MEM_GB, MAIN_MEM_GB (address-space cap per lean process, default 3000; imports are mmapped), GROUP_LEAVES (default 3000), SEG_LEAVES (leaves per kernel check, default 4), OUTDIR (default results/PKG),
#      MIN_AVAIL_GB / KILL_AVAIL_GB (memory-aware scheduling, 0 = off; each worker needs about 3 GB for n = 28)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
CERT=$(cd "$1" && pwd); PKG=$2; N=$3; A=$4; B=$5; W=${6:-$(nproc)}
cd "$ROOT"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
ulimit -n 65536 2>/dev/null || true
OUT=${OUTDIR:-$ROOT/results/$PKG}; mkdir -p "$OUT"
lake build AutocorrK Autocorr.KSound.Run Autocorr.Reduction Autocorr.RealForm
python3 tools/kc_jobs.py "$CERT" "$PKG" --workers "$W" --group-leaves "${GROUP_LEAVES:-3000}" \
  --seg-leaves "${SEG_LEAVES:-4}" | tee "$OUT/export.log"
python3 tools/forms.py "$PKG" "$N" "$A" "$B" > /dev/null
python3 tools/build_dag.py . "$PKG" --jobs "$W" --main "Autocorr.$PKG.Main" --mem-gb "${MEM_GB:-3000}" --main-mem-gb "${MAIN_MEM_GB:-3000}" \
  --tstack 1048576 --min-avail-gb "${MIN_AVAIL_GB:-0}" --kill-avail-gb "${KILL_AVAIL_GB:-0}" \
  --log "$OUT/build.jsonl" | tee "$OUT/build.log"
printf 'import Autocorr.%s.Forms\n#print axioms Autocorr.%s.autocorr_lower\n#print axioms Autocorr.%s.autocorr_lower_ess\n#print axioms Autocorr.%s.autocorr_lower_real\n' \
  "$PKG" "$PKG" "$PKG" "$PKG" > "$OUT/axioms.lean"
lake env lean "$OUT/axioms.lean" > "$OUT/axioms.txt"
echo "axioms written to $OUT/axioms.txt"
