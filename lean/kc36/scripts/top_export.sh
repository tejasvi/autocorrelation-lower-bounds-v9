#!/bin/bash
# KC36, the top of the tree: export the 620 assembly jobs as one top module plus kernel-check chunk modules
# (--split-checks 2000 gave 78 chunks), then the further forms (tools/forms.py) and the merge of Main.lean and Forms.lean
# into the top module (tools/merge_top.py, no in-module axiom report; the per-module scan replaces it).
# usage (from lean/kc36):  scripts/top_export.sh TOPCERT KEXT JOBS
#   TOPCERT  meta.json + jobs/ of the 620 assembly jobs; KEXT  results/KC36/kext.json.gz, uncompressed (the subtree
#            roots built by the shards, reached as external modules); JOBS  parallel export workers
set -u
TOP=$1; KEXT=$2; J=$3
python3 -I tools/kc_shard.py "$TOP" KC36 --workers "$J" --group-leaves 1000 --seg-leaves 1 \
  --external "$KEXT" --main --single-group --split-checks 2000 || exit 1
python3 -I tools/forms.py KC36 36 133 100 || exit 1
python3 -I tools/merge_top.py . KC36 || exit 1
