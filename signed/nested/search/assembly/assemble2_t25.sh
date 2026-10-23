#!/bin/bash
# tau = 1/4 assembly, V22d: same as assemble_t25.sh 31962355 but with mirror2.py (empty-leaf 'boxes' fix) (run on the assembly VM inside the unpacked bundle dir, with the phase-A data unpacked to ./prod25A and
# all worker outputs copied to ./B/*.jsonl).  usage: ./assemble_t25.sh NS   -> cert_t25.json.gz + cert_t25_sub_###.json.gz
set -e; cd "$(dirname "$0")"
sha256sum -c BUNDLE_SHA256SUMS --quiet
ns=${1:-256}
venv/bin/python -I mirror2.py 'prod25A/A/A_*.jsonl' 'B/*.jsonl' A_sym.jsonl B_sym.jsonl
venv/bin/python -I stream_assemble.py cfg25t.json 1/4 prod25A/coarseE.jsonl A_sym.jsonl B_sym.jsonl asm_work cert_t25.json.gz "$ns" cert_t25_sub
