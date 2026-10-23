#!/bin/bash
# usage: tools/build_shards.sh JOBS [LISTFILE]   (run in the project directory on a VM)
# Compiles C64Data/Glob.lean and the arc modules C64Data/A<i>.lean (native_decide with the precompiled checker) in
# parallel; LISTFILE (one module name per line, e.g. A0123) restricts the arc modules (default: all, largest first).
# Per-module logs and times: results/shards/A<i>.log (last line "OK ms" or "FAIL ms").
set -u
J=${1:-40}
LIST=${2:-}
D=.lake/build/lib/lean
LP=$(lake env printenv LEAN_PATH)
DYN="--load-dynlib=$D/LeanC64_C64Core_Ival.so --load-dynlib=$D/LeanC64_C64Core_Num.so --load-dynlib=$D/LeanC64_C64Core_Check.so"
mkdir -p results/shards $D/C64Data
export LEAN_PATH=$LP LEAN_NUM_THREADS=1
one() {
  m=$1; t0=$(date +%s%N)
  if lean $DYN -o .lake/build/lib/lean/C64Data/$m.olean C64Data/$m.lean > results/shards/$m.log 2>&1; then st=OK; else st=FAIL; fi
  echo "$st $(( ($(date +%s%N) - t0) / 1000000 ))" >> results/shards/$m.log
}
export -f one; export DYN
[ -f $D/C64Data/Glob.olean ] || one Glob
if [ -n "$LIST" ]; then cat "$LIST"; else ls -S C64Data | grep '^A[0-9]*\.lean$' | sed 's/\.lean$//'; fi | xargs -P $J -I{} bash -c 'one {}'
grep -l '^FAIL' results/shards/*.log | wc -l
