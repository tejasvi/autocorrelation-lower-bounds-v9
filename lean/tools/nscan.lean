import Lean
/-!
Per-module axiom scan for a sharded NATIVE package (native_decide per job; no import of the closure).

usage: lean --run nscan.lean LIST OUT PREFIX
  LIST    file with one .olean path per line; OUT  report file;
  PREFIX  the package namespace with a trailing dot, e.g. `Autocorr.KC36.`
For every constant of every listed module (read with `readModuleData`, no environment):
  * an `axiom` declaration is allowed only if it is a native_decide auxiliary axiom of the package (name PREFIX...
    ending in `._native.native_decide.ax_1_1`, type `@Eq Bool lhs true`); these are counted by the head constant of
    lhs (expected: the certificate checker); any other axiom is a violation;
  * a reference (in its type or value) to `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`
    is a violation, and so is a reference to a `_native` constant outside PREFIX;
  * every referenced constant outside PREFIX is recorded as an external reference.
OUT gets the module/constant counts, the violations and the sorted external references.  The axioms of the external
references are then checked in a session that imports only the hand-written library, so the whole closure's axioms are
those plus the package's native_decide auxiliary axioms.
-/
open Lean

def bannedNames : List String := ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]

def banned (pre : String) (n : Name) : Bool :=
  let s := n.toString
  bannedNames.contains s || ((s.splitOn "_native").length > 1 && !s.startsWith pre)

def nativeAx (pre : String) (c : ConstantInfo) : Option Name :=
  let s := c.name.toString
  if s.startsWith pre && s.endsWith "._native.native_decide.ax_1_1" then
    match c.type.eq? with
    | some (ty, lhs, rhs) =>
      if ty.isConstOf ``Bool && rhs.isConstOf ``Bool.true then
        -- lhs = `Decidable.decide p inst`: report the head of the decided proposition p (`f .. = true` -> f)
        let lhs' := if lhs.isAppOf ``Decidable.decide then lhs.getArg! 0 else lhs
        match lhs'.eq? with
        | some (_, l, _) => some l.getAppFn.constName
        | none => some lhs'.getAppFn.constName
      else none
    | none => none
  else none

def main (args : List String) : IO UInt32 := do
  let [list, out, pre] := args | do IO.eprintln "usage: kscan LIST OUT PREFIX"; return 2
  let files := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let mut ext : NameSet := {}
  let mut viol : Array String := #[]
  let mut nmods := 0
  let mut nconst := 0
  let mut heads : Std.HashMap Name Nat := {}
  for f in files do
    let (md, _region) ← readModuleData f      -- regions stay mapped until exit (one mapping per module)
    nmods := nmods + 1
    for c in md.constants do
      nconst := nconst + 1
      if c matches .axiomInfo _ then
        match nativeAx pre c with
        | some h => heads := heads.insert h (heads.getD h 0 + 1)
        | none => viol := viol.push s!"axiom {c.name} in {f}"
      let mut used := c.type.getUsedConstants
      if let some v := c.value? then
        used := used ++ v.getUsedConstants
      for u in used do
        if banned pre u then
          viol := viol.push s!"{c.name} uses {u} ({f})"
        else if !(u.toString.startsWith pre) then
          ext := ext.insert u
  let lines := ext.toList.map toString |>.toArray.qsort (· < ·)
  let hs := heads.toList.map (fun (h, k) => s!"{h} {k}") |>.toArray.qsort (· < ·)
  IO.FS.writeFile out (s!"modules {nmods} constants {nconst} violations {viol.size}\n" ++
    "native_axioms_by_checker\n" ++ String.intercalate "\n" hs.toList ++ "\nviolations\n" ++
    String.intercalate "\n" viol.toList ++ (if viol.isEmpty then "" else "\n") ++
    "external\n" ++ String.intercalate "\n" lines.toList ++ "\n")
  return 0
