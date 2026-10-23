import Lean
/-!
Per-module axiom scan for a sharded kernel-only package (no import of the closure).

usage: lean --run kscan.lean LIST OUT PREFIX
  LIST    file with one .olean path per line; OUT  report file;
  PREFIX  the package namespace with a trailing dot, e.g. `Autocorr.KC36.`
For every constant of every listed module (read with `readModuleData`, no environment):
  * an `axiom` declaration is a violation;
  * a reference (in its type or value) to `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`
    or to a constant whose name contains `_native` is a violation;
  * every referenced constant outside PREFIX is recorded as an external reference.
OUT gets the module/constant counts, the violations and the sorted external references.  The axioms of the external
references are then checked with `#print axioms` in a session that imports only the hand-written library, so the
whole closure's axioms are the union of those (no module of the package declares an axiom).
-/
open Lean

def bannedNames : List String := ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]

def banned (n : Name) : Bool :=
  let s := n.toString
  bannedNames.contains s || (s.splitOn "_native").length > 1

def main (args : List String) : IO UInt32 := do
  let [list, out, pre] := args | do IO.eprintln "usage: kscan LIST OUT PREFIX"; return 2
  let files := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut ext : NameSet := {}
  let mut viol : Array String := #[]
  let mut nmods := 0
  let mut nconst := 0
  for f in files do
    let (md, _region) ← readModuleData f      -- regions stay mapped until exit (one mapping per module)
    nmods := nmods + 1
    for c in md.constants do
      nconst := nconst + 1
      if c matches .axiomInfo _ then
        viol := viol.push s!"axiom {c.name} in {f}"
      let mut used := c.type.getUsedConstants
      if let some v := c.value? then
        used := used ++ v.getUsedConstants
      for u in used do
        if banned u then
          viol := viol.push s!"{c.name} uses {u} ({f})"
        else if !(u.toString.startsWith pre) then
          ext := ext.insert u
  let lines := ext.toList.map toString |>.toArray.qsort (· < ·)
  IO.FS.writeFile out (s!"modules {nmods} constants {nconst} violations {viol.size}\n" ++
    String.intercalate "\n" viol.toList ++ (if viol.isEmpty then "" else "\n") ++
    "external\n" ++ String.intercalate "\n" lines.toList ++ "\n")
  return 0
