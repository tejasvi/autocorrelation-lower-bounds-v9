import AutocorrCert.Checker

/-!
# Extended checker: square-cut rows (format 2, checked in Python by `checker/verify_cmp.py`)

The `c30_132m` certificates add one row type, carried inline by leaf records: for integers `v0, v_a` and
blocks `B_a`,

  `Σ_{a,b} v_a v_b [m_{B_a} m_{B_b}] + 2 v0 Σ_a v_a m_{B_a} ≥ -v0²`,

where `[m_D m_E]` is the product column `canon D E`; at the true point the left side plus `v0²` is
`(v0 + Σ_a v_a m_{B_a})² ≥ 0`.  Keys are `XKey.base` (the rows of `Checker.lean`) or `XKey.sq`; everything
else (bound, stack machine, jobs) is as in `Checker.lean`, with `XKey` in place of `RowKey`.  The duals of a
compressed leaf (`D` records: P, G, ZA duals completed by the verifier) are completed by the exporter and are
untrusted data here, like all duals.
-/

namespace Autocorr.Cert

inductive XKey where
  | base (k : RowKey)
  | sq (v0 : Int) (terms : List (Nat × Int))

def keyOKX (sp : Spec) : XKey → Bool
  | .base k => keyOK sp k
  | .sq _ terms => terms.all (fun t => t.1 < sp.nB)

/-- Entries of the square-cut row (`verify_cmp.Spec.sq_row`). -/
def sqEnt (sp : Spec) (v0 : Int) : List (Nat × Int) → List (Nat × Rat)
  | [] => []
  | (b, v) :: rest => (sp.canon b b, (v : Rat) * v) :: (b, 2 * (v0 : Rat) * v) ::
      (rest.map (fun t => (sp.canon b t.1, 2 * (v : Rat) * t.2)) ++ sqEnt sp v0 rest)

def rowOfX (sp : Spec) (bx : Box) : XKey → Row
  | .base k => rowOf sp bx k
  | .sq v0 terms => ⟨some (-((v0 : Rat) * v0)), none, sqEnt sp v0 terms⟩

/-- Add the contribution of one dual entry `(key, y)` (as `dualStep`). -/
def dualStepX (sp : Spec) (bx : Box) (st : Rat × Array Rat) (ky : XKey × Rat) : Rat × Array Rat :=
  if keyOKX sp ky.1 && entOK sp (rowOfX sp bx ky.1).ent then
    if 0 < ky.2 then
      match (rowOfX sp bx ky.1).lo with
      | some l => (st.1 + ky.2 * l, scatter st.2 (-ky.2) (rowOfX sp bx ky.1).ent)
      | none => st
    else if ky.2 < 0 then
      match (rowOfX sp bx ky.1).up with
      | some u => (st.1 + ky.2 * u, scatter st.2 (-ky.2) (rowOfX sp bx ky.1).ent)
      | none => st
    else st
  else st

def dualBoundX (sp : Spec) (bx : Box) (obj : Bool) (ys : List (XKey × Rat)) : Rat :=
  let r0 := Array.replicate sp.NC (0 : Rat)
  let r0 := if obj then r0.setIfInBounds sp.oT 1 else r0
  let st := ys.foldl (dualStepX sp bx) (0, r0)
  st.1 + colPart sp bx st.2

/-- Completion of the duals of a compressed leaf (`verify_cmp.complete_duals`): the P, G and ZA duals that
make the reduced costs of the G, P and own ZA columns vanish (`zo`: the ZA rows, parents first).  Untrusted:
the bound is evaluated (and the soundness proof applies) for whatever list results. -/
def completeX (sp : Spec) (bx : Box) (zo : List RowKey) (ys : List (XKey × Rat)) : List (XKey × Rat) :=
  let r := (ys.foldl (dualStepX sp bx) (0, Array.replicate sp.NC (0 : Rat))).2
  let m := 2 * sp.n - 1
  let gs : List (Nat × Rat) := (List.range m).foldl (fun acc i =>
      let c := m - 1 - i
      let prev := match acc with | [] => 0 | (_, y) :: _ => y
      (c, prev + r.getD (sp.oG + c) 0) :: acc) []
  let gp : List (XKey × Rat) := gs.foldr (fun cy acc =>
      (.base (.G cy.1), cy.2) :: (.base (.P cy.1), cy.2 + r.getD (sp.oP + cy.1) 0) :: acc) []
  let za := zo.foldl (fun (st : Array Rat × List (XKey × Rat)) k =>
      match k with
      | .ZA d e _ =>
        let y := st.1.getD (sp.canon d e) 0
        (scatter st.1 (-y) (rowOf sp bx k).ent, (.base k, y) :: st.2)
      | _ => st) (r, [])
  gp ++ za.2

inductive RecX where
  | split (b : Nat) (s : Rat)
  | leaf (ys : List (XKey × Rat))
  | farkas (ys : List (XKey × Rat))
  | deleg
  /-- A compressed leaf: the listed duals plus `completeX` of them. -/
  | leafc (ys : List (XKey × Rat))

def runX (sp : Spec) (lam : Rat) (zo : List RowKey) : List RecX → List Box → Option (List Box)
  | [], stk => some stk
  | _ :: _, [] => none
  | .split b s :: rs, bx :: stk =>
    runX sp lam zo rs ((child sp bx b s true).toList ++ (child sp bx b s false).toList ++ stk)
  | .leaf ys :: rs, bx :: stk =>
    if lam ≤ dualBoundX sp bx true ys then runX sp lam zo rs stk else none
  | .farkas ys :: rs, bx :: stk =>
    if 0 < dualBoundX sp bx false ys then runX sp lam zo rs stk else none
  | .deleg :: rs, bx :: stk => (runX sp lam zo rs stk).map (bx :: ·)
  | .leafc ys :: rs, bx :: stk =>
    if lam ≤ dualBoundX sp bx true (ys ++ completeX sp bx zo ys) then runX sp lam zo rs stk else none

def checkJobX (sp : Spec) (lam : Rat) (zo : List RowKey) (root : Path) (children : List Path)
    (recs : List RecX) : Bool :=
  sp.wf && decide (lam ≤ 3) &&
  match regionOfPath sp root with
  | none => true
  | some R => decide (runX sp lam zo recs [R] = some (children.filterMap (regionOfPath sp)))

end Autocorr.Cert
