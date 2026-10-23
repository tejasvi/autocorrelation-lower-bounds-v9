# Optional sampled mode

iv_verify.py has an optional sampled mode. It was not used for the results in README.md, which come from full runs.
A sampled run never prints "VERIFIED"; it ends with "SAMPLED-OK (not a full check)".

## What stays complete

The structure pass and the partition are always complete:
- every record of every job file;
- exact regions;
- the stack discipline;
- unique root paths, delegations matched to job roots, and reachability.

The sampling applies only to the leaf certification.

## The sample

A leaf is identified by (job file name, ordinal k of the leaf among that file's leaf records). The selected leaves get
exactly the test of a full run. A leaf is selected by any of three rules:
- **A.** It is listed in --thin-jobs (all leaves of those jobs) or in --thin-leaves (lines "jobname k").
- **B.** int(SHA256(seed || job || "/" || k)[0:8]) < P * 2^64, where P is given by --sample-p as a rational string.
- **C.** It has the smallest SHA256(seed || job || "/" || k) within its job, so every job contributes at least one
  leaf.

## The seed

seed = SHA256("C1-tree-sample-v1" || H || R), where:
- H = SHA256(meta.json || the sorted lines "name sha256(file)" of all job files), computed by the program;
- R comes from --sample-R as hex.

R must be fixed only after H is published. A seed derived from H alone could be steered by re-encoding harmless
details of the certificate until the sample avoids a chosen leaf.

## What a clean sample shows

Let B be the number of leaves that the checker cannot certify. The uniform part misses all of them with probability
(1 - P)^B <= exp(-P*B). At P = 1/100, a clean sample shows B <= 460 with 99% confidence.

It cannot show B = 0, and a single uncertified leaf would invalidate the proof. A sampled run is evidence, not a
verification.

## Combining sampled shards

--combine accepts sampled shard outputs only if all of them carry the same sampling settings (P, H, R, seed and the
hashes of the part-A lists). It then prints the SAMPLED-OK line.
