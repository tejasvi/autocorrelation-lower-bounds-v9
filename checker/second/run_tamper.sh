#!/bin/bash
# run_tamper.sh TAMPERDIR WORKERS [extra verifier args]: run the verifier on every variant (fail-fast);
# the test passes for a variant iff the variant is rejected
D=$1; W=${2:-4}; shift 2
cd "$(dirname "$(readlink -f "$0")")"
PY=${PY:-venv/bin/python}
for v in $(ls -d $D/*/ | xargs -n1 basename); do
  out=$(nice -n 10 $PY -I iv_verify.py $D/$v --workers $W --failfast "$@" 2>&1)
  rc=$?
  verdict=$(echo "$out" | grep -E '^(VERIFIED|NOT VERIFIED)' | tail -1)
  reason=$(echo "$out" | grep -E '^(FAIL|NOT VERIFIED)' | head -1 | cut -c1-220)
  if [ $rc -ne 0 ] && echo "$verdict" | grep -q '^NOT VERIFIED'; then res=REJECTED; else res="ACCEPTED(!)"; fi
  echo "$v | $res | rc=$rc | $reason"
done
