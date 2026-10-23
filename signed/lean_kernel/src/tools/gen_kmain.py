#!/usr/bin/env python3
"""Write KData/Main.lean: the kernel-only proof of the three statements of C64.Defs.

Every arc i has `KData.A<i>.ok : C64KChk.checkArc KData.glob KData.A<i>.arc = true` (module KData.A<i> for E arcs,
KData.A<i>_Ok otherwise, as written by gen_kshards.py), and KData.GlobOK has `C64KChk.checkGlob glob = true`.
The simulation lemmas C64KChk.checkArc_eq / checkGlob_eq turn them into the checker's statements, and the
soundness proof (C64.Check.SoundMain) gives the statements; the AllOK list is in groups of 100, as in gen_main.py.

usage: gen_kmain.py N_ARCS OUTDIR TAU KPLAN.json [KPLAN.json ...]   (TAU as "7 / 30")
"""
import json, os, sys
from fractions import Fraction

n = int(sys.argv[1]); out = sys.argv[2]; tau = sys.argv[3]
okmod = {}
for p in sys.argv[4:]:
    for i, v in json.load(open(p))["arcs"].items():
        okmod[int(i)] = v["ok"]
assert sorted(okmod) == list(range(n)), "plans do not cover the arcs 0..n-1"
tn, td = (int(x) for x in tau.split("/"))
K = 1 / (1 - Fraction(tn, td))
KS = f"{K.numerator}/{K.denominator}"
G = 100
L = ["import C64.Check.SoundMain\nimport C64K.KChkSim2\nimport KData.GlobOK\n"]
L += [f"import KData.{okmod[i]}\n" for i in range(n)]
L.append("\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nopen C64Chk\n\nnamespace KData\n\n")
L.append("/-- Every arc of the list passes the checker. -/\ndef AllOK (g : Glob) : List Arc → Prop\n  | [] => True\n"
         "  | a :: as => checkArc g a = true ∧ AllOK g as\n\n")
L.append("theorem AllOK.mem {g : Glob} : ∀ {l : List Arc}, AllOK g l → ∀ a ∈ l, checkArc g a = true\n"
         "  | [], _, a, ha => by simp at ha\n"
         "  | b :: l, h, a, ha => by\n"
         "    simp only [List.mem_cons] at ha\n"
         "    rcases ha with rfl | ha\n"
         "    · exact h.1\n"
         "    · exact AllOK.mem h.2 a ha\n\n")
L.append("theorem AllOK.append {g : Glob} : ∀ {l₁ l₂ : List Arc}, AllOK g l₁ → AllOK g l₂ → AllOK g (l₁ ++ l₂)\n"
         "  | [], _, _, h₂ => h₂\n"
         "  | _ :: _, _, h₁, h₂ => ⟨h₁.1, AllOK.append h₁.2 h₂⟩\n\n")
L.append("/-- A kernel-checked arc of the port is an arc of the checker (the simulation lemma). -/\n"
         "theorem kok {a : Arc} (h : C64KChk.checkArc glob a = true) : checkArc glob a = true :=\n"
         "  (C64KChk.checkArc_eq glob a) ▸ h\n\n")
L.append("theorem globOK' : checkGlob glob = true := (C64KChk.checkGlob_eq glob) ▸ globOK\n\n")
groups = [list(range(k, min(k + G, n))) for k in range(0, n, G)]
for gi, grp in enumerate(groups):
    L.append(f"def arcs{gi} : List Arc := [" + ", ".join(f"A{i:04d}.arc" for i in grp) + "]\n")
    L.append(f"theorem ok{gi} : AllOK glob arcs{gi} := ⟨" + ", ".join(f"kok A{i:04d}.ok" for i in grp) + ", trivial⟩\n\n")
lst = f"arcs{len(groups)-1}"
for gi in range(len(groups) - 2, -1, -1):
    lst = f"arcs{gi} ++ ({lst})"
L.append("/-- The arcs of the certificate, in order of `s₀`. -/\ndef arcs : List Arc := " + lst + "\n\n")
okterm = f"ok{len(groups)-1}"
for gi in range(len(groups) - 2, -1, -1):
    okterm = f"AllOK.append ok{gi} ({okterm})"
L.append(f"theorem arcs_ok : AllOK glob arcs := {okterm}\n\n")
L.append("theorem cover_ok : coverOK glob 0 (arcs.map fun a => (a.s0, a.s1)) = true := by decide +kernel\n\n")
L.append(f"theorem tau_val : glob.tau.val = {tau} := by norm_num [glob, Q.val]\n\n")
L.append(f"/-- Theorem 1.3 of the paper (one-sided, strict): `ess sup (f ⋆ f) > ({KS}) (∫ f)²`, kernel-only. -/\n"
         "theorem mainStatement : C64.MainStatement :=\n"
         "  mainStatement_of tau_val (main_of_checks globOK' cover_ok (AllOK.mem arcs_ok))\n\n")
L.append("theorem mainStatementEss : C64.MainStatementEss := mainStatementEss_of mainStatement\n\n")
L.append(f"/-- `C₃ ≥ C₃' ≥ {KS}`. -/\ntheorem constStatement : C64.ConstStatement := constStatement_of mainStatement\n\n")
L.append("end KData\n")
os.makedirs(os.path.join(out, "KData"), exist_ok=True)
open(os.path.join(out, "KData", "Main.lean"), "w").write("".join(L))
print("wrote", os.path.join(out, "KData", "Main.lean"), "arcs", n, "groups", len(groups))
