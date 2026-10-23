#!/bin/bash
# KC36, after all shard modules are in .lake/build/lib/lean and the top export is done: compile Params and the check
# chunks (top module, Main and Forms excluded), then the top module itself in one process (it imports all 2,274,565
# other modules: in production 49 min of wall time and 2.6 TiB resident after a page prefetch of every compiled module
# with ../tools/prefetch_olean.py, read-ahead off), then the per-module axiom scan and the axioms of the external references.
# usage (from lean/kc36):  scripts/top_build.sh JOBS SCANDIR
set -u
J=$1; S=$2
LP=${LEAN_PATH:-$(lake env printenv LEAN_PATH)}
D=.lake/build/lib/lean
printf "Autocorr.KC36.Gro.Groot\nAutocorr.KC36.Main\nAutocorr.KC36.Forms\n" > top_exclude.txt
python3 -I tools/build_dag.py . KC36 --jobs "$J" --lean-path "$LP" --mem-gb 100000 --main-mem-gb 100000 \
  --exclude top_exclude.txt --rm-src || exit 1
LEAN_PATH=$LP lean -o $D/Autocorr/KC36/Gro/Groot.olean Autocorr/KC36/Gro/Groot.lean || exit 1
sha256sum $D/Autocorr/KC36/Gro/Groot.olean
mkdir -p "$S"
find $D/Autocorr/KC36 -name "*.olean" | sort > "$S/all.txt"
split -n l/"$J" -d -a 3 "$S/all.txt" "$S/part_"
for f in "$S"/part_???; do
  (LEAN_PATH=$LP lean --run tools/kscan.lean "$f" "$f.out" Autocorr.KC36. > "$f.log" 2>&1; echo "rc=$?" >> "$f.log") &
done
wait
grep -h "^modules" "$S"/part_*.out | awk '{m+=$2; c+=$4; v+=$6} END {print "modules", m, "constants", c, "violations", v}'
for f in "$S"/part_*.out; do sed -n '/^external/,$p' "$f" | tail -n +2; done | sort -u > "$S/external.txt"
KSCAN_EXT="$S/external.txt" LEAN_PATH=$LP lean tools/kscan_ext.lean 2>&1 | tail -3
