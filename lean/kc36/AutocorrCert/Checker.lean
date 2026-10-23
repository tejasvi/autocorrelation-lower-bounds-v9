/-!
# Certificate checker for `HalfClaim n lam` (computable; core Lean only)

This mirrors the Python checker `checker/verify.py`:

* `Spec`: the balanced binary block tree of `Spec(n)` (preorder numbering), computed by `buildTree`.
  The soundness proof uses only the Boolean well-formedness check `Spec.wf`.
* Columns (dense layout): `m_b` (`b < nB`), `Z_ij` at `oZ + min(i,j)·n + max(i,j)`,
  `ZA_de` at `oZA + min(d,e)·nB + max(d,e)`, `P_c` at `oP + c`, `G_c` at `oG + c`, `t` at `oT`.
  Leaf–leaf products `m_d m_e` are the `Z` columns (`Spec.canon`), as in `verify.Spec.canon_pair`.
* Rows are built from semantic keys (`rowOf`), with exact rational coefficients.
* `dualBound`: the Neumaier–Shcherbina bound `Σ_r y_r (lo_r or up_r) + Σ_c min(r_c lb_c, r_c ub_c)`,
  `r = e_t − Aᵀy`; rows with an invalid key, an inadmissible sign, or an out-of-range column are
  dropped (same as `y_r = 0`).
* `propagate`: exact interval propagation on the tree (root mass 1), at most 64 sweeps.
* `run`: the DFS stack machine over records (`split`, `leaf`, `farkas`); child 1 is processed first.
-/

namespace Autocorr.Cert

/-- A block `[lo, hi)` of bins with children `c1, c2` (meaningful only if `lo + 1 < hi`). -/
structure Blk where
  lo : Nat
  hi : Nat
  c1 : Nat
  c2 : Nat
deriving Repr, Inhabited, DecidableEq

/-- `verify.Spec.__init__.build`: preorder construction of the balanced split tree. -/
def buildAux : Nat → Nat → Nat → Array Blk → Array Blk
  | 0, _, _, acc => acc
  | fuel + 1, lo, hi, acc =>
    let idx := acc.size
    let acc := acc.push ⟨lo, hi, 0, 0⟩
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      let a := acc.size
      let acc := buildAux fuel lo mid acc
      let b := acc.size
      let acc := buildAux fuel mid hi acc
      acc.setIfInBounds idx ⟨lo, hi, a, b⟩
    else acc

def buildTree (n : Nat) : Array Blk := buildAux (n + 1) 0 n #[]

/-- Index of the leaf block `[i, i+1)`. -/
def findLeaf (t : Array Blk) (i : Nat) : Nat :=
  (t.findIdx? (fun B => B.lo == i && B.hi == i + 1)).getD 0

structure Spec where
  n : Nat
  tree : Array Blk
  leafOf : Array Nat

def mkSpec (n : Nat) : Spec :=
  let t := buildTree n
  ⟨n, t, ((List.range n).map (findLeaf t)).toArray⟩

namespace Spec

variable (sp : Spec)

def nB : Nat := sp.tree.size
def blk (b : Nat) : Blk := sp.tree.getD b default
def isInt (b : Nat) : Bool := (sp.blk b).lo + 1 < (sp.blk b).hi
def isLeaf (b : Nat) : Bool := (sp.blk b).hi == (sp.blk b).lo + 1
def leaf (i : Nat) : Nat := sp.leafOf.getD i 0

def oZ : Nat := sp.nB
def oZA : Nat := sp.oZ + sp.n * sp.n
def oP : Nat := sp.oZA + sp.nB * sp.nB
def oG : Nat := sp.oP + (2 * sp.n - 1)
def oT : Nat := sp.oG + (2 * sp.n - 1)
def NC : Nat := sp.oT + 1

def zIdx (i j : Nat) : Nat := sp.oZ + min i j * sp.n + max i j
def zaIdx (d e : Nat) : Nat := sp.oZA + min d e * sp.nB + max d e
/-- Column of the product `m_d m_e` (`verify.Spec.canon_pair`). -/
def canon (d e : Nat) : Nat :=
  if sp.isLeaf d && sp.isLeaf e then sp.zIdx (sp.blk d).lo (sp.blk e).lo else sp.zaIdx d e

/-- Well-formedness of the block tree (the only property of `buildTree` the proof uses). -/
def wf : Bool :=
  0 < sp.n && 0 < sp.nB && (sp.blk 0).lo == 0 && (sp.blk 0).hi == sp.n &&
  (List.range sp.nB).all (fun b =>
    (sp.blk b).lo < (sp.blk b).hi && (sp.blk b).hi ≤ sp.n &&
    ((sp.blk b).hi == (sp.blk b).lo + 1 ||
      ((sp.blk b).c1 < sp.nB && (sp.blk b).c2 < sp.nB &&
        (sp.blk (sp.blk b).c1).lo == (sp.blk b).lo &&
        (sp.blk (sp.blk b).c1).hi == (sp.blk (sp.blk b).c2).lo &&
        (sp.blk (sp.blk b).c2).hi == (sp.blk b).hi))) &&
  (List.range sp.n).all (fun i =>
    sp.leaf i < sp.nB && (sp.blk (sp.leaf i)).lo == i && (sp.blk (sp.leaf i)).hi == i + 1)

end Spec

/-- A region: bounds `L_b ≤ m_b ≤ U_b` on the block masses. -/
structure Box where
  L : Array Rat
  U : Array Rat
deriving DecidableEq, Repr, Inhabited

/-! ## Interval propagation (`verify.Spec.propagate`) -/

/-- One update at block `b` (all six values computed from the old ones). -/
def sweepB (sp : Spec) (st : Array Rat × Array Rat × Bool) (b : Nat) : Array Rat × Array Rat × Bool :=
  if sp.isInt b then
    let L := st.1
    let U := st.2.1
    let c1 := (sp.blk b).c1
    let c2 := (sp.blk b).c2
    let Lb := L.getD b 0
    let Ub := U.getD b 0
    let L1 := L.getD c1 0
    let U1 := U.getD c1 0
    let L2 := L.getD c2 0
    let U2 := U.getD c2 0
    let nl := max Lb (L1 + L2)
    let nu := min Ub (U1 + U2)
    let l1 := max L1 (Lb - U2)
    let u1 := min U1 (Ub - L2)
    let l2 := max L2 (Lb - U1)
    let u2 := min U2 (Ub - L1)
    let same := nl == Lb && nu == Ub && l1 == L1 && u1 == U1 && l2 == L2 && u2 == U2
    (((L.setIfInBounds b nl).setIfInBounds c1 l1).setIfInBounds c2 l2, ((U.setIfInBounds b nu).setIfInBounds c1 u1).setIfInBounds c2 u2, st.2.2 || !same)
  else st

def sweep (sp : Spec) (L U : Array Rat) : Array Rat × Array Rat × Bool :=
  (List.range sp.nB).foldl (sweepB sp) (L, U, false)

def propLoop (sp : Spec) : Nat → Array Rat → Array Rat → Array Rat × Array Rat
  | 0, L, U => (L, U)
  | k + 1, L, U =>
    let r := sweep sp L U
    if r.2.2 then propLoop sp k r.1 r.2.1 else (r.1, r.2.1)

/-- Root mass 1, then at most 64 sweeps; `none` if the box is empty. -/
def propagate (sp : Spec) (L U : Array Rat) : Option Box :=
  let L := L.setIfInBounds 0 (max (L.getD 0 0) 1)
  let U := U.setIfInBounds 0 (min (U.getD 0 0) 1)
  let r := propLoop sp 64 L U
  if (List.range sp.nB).all (fun b => r.1.getD b 0 ≤ r.2.getD b 0) then some ⟨r.1, r.2⟩ else none

def rootBox (sp : Spec) : Option Box :=
  propagate sp (Array.replicate sp.nB 0) (Array.replicate sp.nB 1)

/-- Child `side` of the split of block `b` at `s` (`false`: `U_b := s`; `true`: `L_b := s`). -/
def child (sp : Spec) (bx : Box) (b : Nat) (s : Rat) (side : Bool) : Option Box :=
  if side then propagate sp (bx.L.setIfInBounds b s) bx.U else propagate sp bx.L (bx.U.setIfInBounds b s)

/-! ## LP rows (`verify.Spec.row`) -/

inductive RowKey where
  | win (c1 c2 : Nat)
  | P (c : Nat)
  | G (c : Nat)
  | tree (b : Nat)
  | ZA (d e s : Nat)
  | rlt (i : Nat)
  | sym
  | mc (d e q : Nat)
deriving Repr, DecidableEq, Inhabited

/-- `verify.Spec.validate_key`. -/
def keyOK (sp : Spec) : RowKey → Bool
  | .win c1 c2 => c1 ≤ c2 && c2 + 2 ≤ 2 * sp.n
  | .P c => c + 2 ≤ 2 * sp.n
  | .G c => c + 2 ≤ 2 * sp.n
  | .tree b => b < sp.nB && sp.isInt b
  | .ZA d e s => d < sp.nB && e < sp.nB && s < sp.nB && (s == d || s == e) && sp.isInt s
  | .rlt i => i < sp.n
  | .sym => true
  | .mc d e q => d < sp.nB && e < sp.nB && q ≤ 3

/-- A row `lo ≤ Σ a_k x_k ≤ up` (`none` = infinite). Entries may repeat a column (they add up). -/
structure Row where
  lo : Option Rat
  up : Option Rat
  ent : List (Nat × Rat)

def rowOf (sp : Spec) (bx : Box) : RowKey → Row
  | .win c1 c2 =>
    let w : Rat := (2 * (sp.n : Rat)) / ((c2 : Rat) - (c1 : Rat) + 2)
    ⟨none, some 0, (sp.oG + c2, w) :: (sp.oT, -1) ::
      (if 0 < c1 then [(sp.oG + (c1 - 1), -w)] else [])⟩
  | .P c =>
    ⟨some 0, some 0, (sp.oP + c, 1) :: (List.range sp.n).filterMap
      (fun i => if i ≤ c ∧ c - i < sp.n then some (sp.zIdx i (c - i), -1) else none)⟩
  | .G c =>
    ⟨some 0, some 0, (sp.oG + c, 1) :: (sp.oP + c, -1) ::
      (if 0 < c then [(sp.oG + (c - 1), -1)] else [])⟩
  | .tree b => ⟨some 0, some 0, [(b, 1), ((sp.blk b).c1, -1), ((sp.blk b).c2, -1)]⟩
  | .ZA d e s =>
    let o := if s = d then e else d
    let s1 := (sp.blk s).c1
    let s2 := (sp.blk s).c2
    ⟨some 0, some 0, (sp.canon d e, 1) ::
      (if d = e then [(sp.canon s1 s1, -1), (sp.canon s1 s2, -2), (sp.canon s2 s2, -1)]
       else [(sp.canon s1 o, -1), (sp.canon s2 o, -1)])⟩
  | .rlt i => ⟨some 0, some 0, (List.range sp.n).map (fun j => (sp.zIdx i j, 1)) ++ [(sp.leaf i, -1)]⟩
  | .sym => ⟨none, some 0, (List.range sp.n).map
      (fun i => (sp.leaf i, 2 * (i : Rat) - ((sp.n : Rat) - 1)))⟩
  | .mc d e q =>
    let z := sp.canon d e
    let Ld := bx.L.getD d 0
    let Ud := bx.U.getD d 0
    let Le := bx.L.getD e 0
    let Ue := bx.U.getD e 0
    if d = e then
      if q = 0 then ⟨none, some (Ld * Ld), [(z, -1), (d, 2 * Ld)]⟩
      else if q = 1 then ⟨none, some (Ud * Ud), [(z, -1), (d, 2 * Ud)]⟩
      else ⟨none, some (-(Ld * Ud)), [(z, 1), (d, -(Ld + Ud))]⟩
    else
      if q = 0 then ⟨none, some (Ld * Le), [(z, -1), (d, Le), (e, Ld)]⟩
      else if q = 1 then ⟨none, some (Ud * Ue), [(z, -1), (d, Ue), (e, Ud)]⟩
      else if q = 2 then ⟨none, some (-(Ld * Ue)), [(z, 1), (d, -Ue), (e, -Ld)]⟩
      else ⟨none, some (-(Ud * Le)), [(z, 1), (d, -Le), (e, -Ud)]⟩

/-! ## The Neumaier–Shcherbina bound -/

/-- `r_k += c · a` for every entry `(k, a)`. -/
def scatter (r : Array Rat) (c : Rat) : List (Nat × Rat) → Array Rat
  | [] => r
  | (k, a) :: rest => scatter (r.modify k (· + c * a)) c rest

def entOK (sp : Spec) (ent : List (Nat × Rat)) : Bool := ent.all (fun e => e.1 < sp.NC)

/-- Add the contribution of one dual entry `(key, y)`. -/
def dualStep (sp : Spec) (bx : Box) (st : Rat × Array Rat) (ky : RowKey × Rat) : Rat × Array Rat :=
  if keyOK sp ky.1 && entOK sp (rowOf sp bx ky.1).ent then
    if 0 < ky.2 then
      match (rowOf sp bx ky.1).lo with
      | some l => (st.1 + ky.2 * l, scatter st.2 (-ky.2) (rowOf sp bx ky.1).ent)
      | none => st
    else if ky.2 < 0 then
      match (rowOf sp bx ky.1).up with
      | some u => (st.1 + ky.2 * u, scatter st.2 (-ky.2) (rowOf sp bx ky.1).ent)
      | none => st
    else st
  else st

def lbOf (sp : Spec) (bx : Box) (k : Nat) : Rat := if k < sp.oZ then bx.L.getD k 0 else 0
def ubOf (sp : Spec) (bx : Box) (k : Nat) : Rat :=
  if k < sp.oZ then bx.U.getD k 0 else if k < sp.oT then 1 else 3

def colPart (sp : Spec) (bx : Box) (r : Array Rat) : Rat :=
  (List.range sp.NC).foldl
    (fun acc k => acc + min (r.getD k 0 * lbOf sp bx k) (r.getD k 0 * ubOf sp bx k)) 0

/-- NS bound for the objective `t` (`obj = true`) or the zero objective (Farkas, `obj = false`). -/
def dualBound (sp : Spec) (bx : Box) (obj : Bool) (ys : List (RowKey × Rat)) : Rat :=
  let r0 := Array.replicate sp.NC (0 : Rat)
  let r0 := if obj then r0.setIfInBounds sp.oT 1 else r0
  let st := ys.foldl (dualStep sp bx) (0, r0)
  st.1 + colPart sp bx st.2

/-! ## The DFS stack machine (`verify.verify_job`, with delegations flattened) -/

inductive Rec where
  | split (b : Nat) (s : Rat)
  | leaf (ys : List (RowKey × Rat))
  | farkas (ys : List (RowKey × Rat))
  | deleg

/-- The stack machine. `deleg` (an `S` record of verify.py) moves the popped box to the output:
the result lists the delegated boxes (in record order) followed by the final stack. -/
def run (sp : Spec) (lam : Rat) : List Rec → List Box → Option (List Box)
  | [], stk => some stk
  | _ :: _, [] => none
  | .split b s :: rs, bx :: stk =>
    run sp lam rs ((child sp bx b s true).toList ++ (child sp bx b s false).toList ++ stk)
  | .leaf ys :: rs, bx :: stk =>
    if lam ≤ dualBound sp bx true ys then run sp lam rs stk else none
  | .farkas ys :: rs, bx :: stk =>
    if 0 < dualBound sp bx false ys then run sp lam rs stk else none
  | .deleg :: rs, bx :: stk => (run sp lam rs stk).map (bx :: ·)

/-- A segment of the global DFS log: from stack `stkIn` the records end at stack `stkOut`. -/
def checkSeg (sp : Spec) (lam : Rat) (stkIn : List Box) (recs : List Rec) (stkOut : List Box) : Bool :=
  sp.wf && decide (lam ≤ 3) && decide (run sp lam recs stkIn = some stkOut)

/-- A node of the branch-and-bound tree: the splits `(b, s, side)` from the root. -/
abbrev Path := List (Nat × Rat × Bool)

/-- The region of a node, recomputed from the root (`none` if it is empty). -/
def regionOfPath (sp : Spec) (path : Path) : Option Box :=
  path.foldl (fun ob e => ob.bind (fun bx => child sp bx e.1 e.2.1 e.2.2)) (rootBox sp)

/-- One job of the certificate: the subtree at `root`, whose records delegate the subtrees at
`children` (in record order). -/
def checkJob (sp : Spec) (lam : Rat) (root : Path) (children : List Path) (recs : List Rec) : Bool :=
  sp.wf && decide (lam ≤ 3) &&
  match regionOfPath sp root with
  | none => true
  | some R => decide (run sp lam recs [R] = some (children.filterMap (regionOfPath sp)))

end Autocorr.Cert
