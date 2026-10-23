"""Fingerprint of the certificate files an exporter reads: meta.json and jobs/*.jsonl.gz.

usage: cert_manifest.py CERTDIR [--workers W]        (an extracted certificate directory)
       cert_manifest.py --tar ARCHIVE.tar            (the same files read from a tar archive, without extracting)

Prints the number of files and the manifest hash, i.e. the SHA-256 of the text with one line
"<sha256 of the file>  <path relative to the certificate root>" per file, sorted by path.  Two certificate copies
with the same manifest hash have byte-identical meta.json and job logs.
"""
import sys, os, glob, hashlib, argparse, tarfile
from multiprocessing import get_context


def sha_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b""):
            h.update(chunk)
    return h.hexdigest()


def manifest_hash(entries):
    text = "".join(f"{h}  {p}\n" for p, h in sorted(entries))
    return hashlib.sha256(text.encode()).hexdigest()


def wanted(rel):
    return rel == "meta.json" or (rel.startswith("jobs/") and rel.endswith(".jsonl.gz") and rel.count("/") == 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("certdir", nargs="?")
    ap.add_argument("--tar", default=None)
    ap.add_argument("--workers", type=int, default=8)
    args = ap.parse_args()
    if args.tar:
        entries = []
        with tarfile.open(args.tar, "r:") as tf:
            for m in tf:
                rel = m.name[2:] if m.name.startswith("./") else m.name
                if m.isfile() and wanted(rel):
                    h = hashlib.sha256()
                    fh = tf.extractfile(m)
                    for chunk in iter(lambda: fh.read(1 << 22), b""):
                        h.update(chunk)
                    entries.append((rel, h.hexdigest()))
    else:
        root = args.certdir
        rels = ["meta.json"] + sorted("jobs/" + os.path.basename(f)
                                      for f in glob.glob(os.path.join(root, "jobs", "*.jsonl.gz")))
        paths = [os.path.join(root, r) for r in rels]
        with get_context("fork").Pool(args.workers) as pool:
            hs = pool.map(sha_file, paths, chunksize=64)
        entries = list(zip(rels, hs))
    print(f"files {len(entries)}  manifest_sha256 {manifest_hash(entries)}")


if __name__ == "__main__":
    main()
