"""Merge the generated Main.lean and Forms.lean of a sharded package into its assembly module, so that the whole import
closure (hundreds of thousands of shard modules) is loaded by one `lean` process instead of three.

usage: merge_top.py ROOT PKG [--report-dir DIR]
  ROOT  the project root; PKG the package (e.g. C36T).  Expects Autocorr/PKG/Main.lean (export_shard.py --main
        --single-group) and Autocorr/PKG/Forms.lean (forms.py).  The assembly module is the one Main.lean imports
        (Autocorr.PKG.G<id[:2]>.G<id>, id = the job with the empty root path).
  After the merge the assembly module also proves the theorems of Main and Forms (same names) and, with --report-dir,
  ends with an #eval that writes DIR/axioms_<theorem>.txt (all axioms) and DIR/axioms_summary.txt; Main.lean and
  Forms.lean become comment-only modules.  The theorem statements are unchanged.
"""
import os, sys, argparse

ap = argparse.ArgumentParser()
ap.add_argument("root")
ap.add_argument("pkg")
ap.add_argument("--report-dir", default=None)
ap.add_argument("--split-checks", type=int, default=0,
                help="move each job's `recs` + `chk` (native_decide; they need only the table module) into this many "
                     "chunk modules <top>_c<k> that build in parallel; the top module keeps the `covered` theorems")
a = ap.parse_args()
B = os.path.join(a.root, "Autocorr", a.pkg)
ns = f"Autocorr.{a.pkg}"
main = open(os.path.join(B, "Main.lean")).read()
forms = open(os.path.join(B, "Forms.lean")).read()
top = [l.split()[1] for l in main.splitlines() if l.startswith(f"import {ns}.G")]
assert len(top) == 1, "Main.lean must import exactly one assembly module"
topfile = os.path.join(a.root, *top[0].split(".")) + ".lean"
imports = [l for l in main.splitlines() + forms.splitlines()
           if l.startswith("import ") and not l.startswith(f"import {ns}.")]
mbody = main.split(f"namespace {ns}\n", 1)[1].rsplit(f"end {ns}", 1)[0]
fbody = forms.split(f"namespace {ns}\n", 1)[1].rsplit(f"end {ns}", 1)[0]
thms = [f"{ns}.autocorr_lower", f"{ns}.autocorr_lower_ess", f"{ns}.autocorr_lower_real"]
tail = (f"\n\n/-! The bound (generated as {ns}.Main and {ns}.Forms; merged here so that the import closure is loaded "
        f"once). -/\n\nopen MeasureTheory ENNReal Set\n\nnamespace {ns}\n" + mbody + fbody + f"end {ns}\n")
if a.report_dir:
    d = os.path.abspath(a.report_dir)
    tail += f'''
/-! Axiom report (written to {d}/axioms_<theorem>.txt; one line per axiom). -/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let mut out : Array String := #[]
  for n in [{", ".join("``" + t for t in thms)}] do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let mut std := 0
    let mut nat := 0
    let mut other : Array Name := #[]
    for a in axs do            -- one linear pass (millions of axioms)
      if a == ``propext || a == ``Classical.choice || a == ``Quot.sound then
        std := std + 1
      else if a.toString.endsWith "._native.native_decide.ax_1_1" then
        nat := nat + 1
      else
        other := other.push a
    out := out.push s!"{{n}}: {{axs.size}} axioms; standard {{std}}; native_decide {{nat}}; other {{other.size}} {{other.toList.take 20}}"
    IO.FS.writeFile s!"{d}/axioms_{{n}}.txt" (String.intercalate "\\n" (axs.toList.map toString) ++ "\\n")
  IO.FS.writeFile "{d}/axioms_summary.txt" (String.intercalate "\\n" out.toList ++ "\\n")
  for l in out do
    IO.println l
'''
tmp = topfile + ".tmp"
if a.split_checks:
    import re
    src = open(topfile).read()
    parts = src.split("\n-- job ")
    header, blocks = parts[0], parts[1:]
    zo = f"import {ns}.Zo"
    hl = header.splitlines()
    assert zo in hl
    K = min(a.split_checks, max(1, len(blocks)))
    chunks, load, covs = [[] for _ in range(K)], [0] * K, []
    for b in blocks:                          # export_shard's job block: recs, chk, covered (post-order)
        nl = int(re.match(r"\S+: (\d+) leaves", b).group(1))
        i = b.index("\ntheorem covered")
        j = b.index(f"\nend {ns}.J", i)
        jns = re.search(rf"\nnamespace ({re.escape(ns)}\.J\S+)\n", b).group(1)
        k = min(range(K), key=lambda x: load[x])
        chunks[k].append("\n-- job " + b[:i] + "\n\nend " + jns + "\n"); load[k] += nl
        covs.append("\nnamespace " + jns + "\n" + b[i:j] + "\nend " + jns + "\n")
    cmod = top[0] + "_c"
    for k in range(K):
        open(topfile[:-5] + f"_c{k}.lean", "w").write(
            f"{zo}\n\nset_option maxRecDepth 100000\n\n-- top checks, chunk {k}: {len(chunks[k])} jobs, {load[k]} leaves\n"
            + "".join(chunks[k]))
    imps = [l for l in hl if l.startswith("import ")]
    body = "".join(l + "\n" for l in dict.fromkeys(imports)) + zo + "\n" + "".join(
        f"import {cmod}{k}\n" for k in range(K)) + "".join(l + "\n" for l in imps if l != zo) + \
        "\nset_option maxRecDepth 100000\n\n-- the covered theorems of the top jobs (their checks are in the chunk modules)\n"
    with open(tmp, "w") as out:
        out.write(body + "".join(covs) + tail)
else:
    with open(tmp, "w") as out, open(topfile) as src:
        out.write("".join(l + "\n" for l in dict.fromkeys(imports)))
        while True:
            chunk = src.read(1 << 26)
            if not chunk:
                break
            out.write(chunk)
        out.write(tail)
os.replace(tmp, topfile)
side = topfile + ".sha256"
if os.path.exists(side):
    os.remove(side)
open(os.path.join(B, "Main.lean"), "w").write(f"/-! The bound is proved in {top[0]} (merged module). -/\n")
open(os.path.join(B, "Forms.lean"), "w").write(f"/-! The further forms are proved in {top[0]} (merged module). -/\n")
print(f"merged into {top[0]} ({os.path.getsize(topfile)} bytes)")
