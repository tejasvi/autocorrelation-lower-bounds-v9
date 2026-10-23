#!/bin/bash
# KC36, one build shard: export with tools/kc_shard.py (group-leaves 1000, seg-leaves 1; pass 1 re-checks every leaf
# exactly against the certificate) and compile the generated modules with tools/build_dag.py. No native code: every
# check is `decide +kernel`.
# usage (from lean/kc36, library built there with `lake build`):  scripts/shard_build.sh CERTDIR JOBS LOG
#   CERTDIR  meta.json + jobs/ of one shard: the filled job files of its subtrees (results/KC36/partition.json.gz lists
#            the 6,372 subtree roots; the filled files are listed in c36t_filled_certificate.sha256.gz, a separate
#            file of the record)
#   JOBS     parallel workers (export and build); LOG  per-module build log (JSON lines)
# The shared module Autocorr.KC36.Params is generated and compiled by every shard (identical each time).
# The production run also passed --min-avail-gb / --kill-avail-gb to build_dag.py (memory guard of a shared server).
set -u
CD=$1; J=$2; LOGF=$3
LP=${LEAN_PATH:-$(lake env printenv LEAN_PATH)}
python3 -I tools/kc_shard.py "$CD" KC36 --workers "$J" --group-leaves 1000 --seg-leaves 1 || exit 1
python3 -I tools/build_dag.py . KC36 --jobs "$J" --lean-path "$LP" --mem-gb 100000 --main-mem-gb 100000 \
  --log "$LOGF" --rm-src || exit 1
