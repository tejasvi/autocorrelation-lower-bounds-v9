import C64Core.Num

/-!
# The certificate checker for GGSTW Problem 6.4 (one-sided, three-level certificates), core Lean only

This mirrors the conditions of the independent checker (`indep3m.py`): type E arcs, type H arcs (one witness), type
H3 arcs (pinned points, a tree of product boxes with exclusion and witness leaves), and the winding number of `S`
along `T₁`.  All numbers are balls at precision `P` (`C64.Ival`), except the exact rational checks on the
witness measures.  Nothing in the data is trusted: every condition is re-derived here, and the soundness proofs
(`C64.Check.Sound*`) turn a `true` result into the hypotheses of the settlement lemmas of `C64.Settle`.

Data layout: an arc header and the leaf tree are Lean terms; the data of a leaf is one natural number read from
the low bits upward, as length-prefixed fields (`rdNat`, `rdInt`).

The functions of `t ∈ [-1/2, 1/2]` are bounded on a binary tree of cells (`cells`); along a branch the values
`K_t(ζ)` at the cell centres are carried by multiplication with `K_{±h}(ζ)`, `h = 2^{-e-1}`, from precomputed
tables (`chain`), since `K_{t+h} = K_t K_h`.
-/

namespace C64Chk

open Ival Ival.Ball C64Num

/-! ## Data -/

/-- A rational number `n / d` (the checker requires `d > 0` where it uses one). -/
structure Q where
  n : Int
  d : Nat
deriving Repr, Inhabited

/-- The leaf tree of a type H arc: product boxes are split in four along the pinned point `j`. -/
inductive Tree where
  | excl (dat : Nat)
  | wit (dat : Nat)
  | split (j : Nat) (c0 c1 c2 c3 : Tree)
deriving Repr, Inhabited

/-- An arc `[s₀, s₁]` of `T₁` (`s = n / 2^ES`): type E with multiplier `u`, or type H with centre `s_c`, pinned
points `p_j` and radii `R_j` (both empty at level 2), a proposed crossing radius `rX` (units `2^-P`; the checker uses
`max (rDisc ..) rX`, which is valid whatever `rX` is) and a leaf tree. -/
inductive Arc where
  | E (s0 s1 : Nat) (ur ui : Int)
  | H (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : Tree)
deriving Repr, Inhabited

/-- Global data: precision and Taylor parameters, the grids of `s` and `q`, `τ`, `T₁ = (c, a, b)` and the tiles
`(c_re, c_im, a, b)`. -/
structure Glob where
  P : Nat
  n : Nat
  k : Nat
  /-- depth of the cells in `t` (smallest cell radius `2^{-D-1}`) -/
  D : Nat
  /-- bisection depths: E arcs, tile arcs, winding pieces -/
  dE : Nat
  dT : Nat
  dW : Nat
  ES : Nat
  EQ : Nat
  tau : Q
  c : Q
  a : Q
  b : Q
  tiles : List (Q × Q × Q × Q)
deriving Repr, Inhabited

def Glob.cfg (g : Glob) : Cfg := ⟨g.P, g.n, g.k⟩

/-! ## Reading fields -/

/-- A natural number: 8 bits of length `L`, then `L` bits. -/
@[inline] def rdNat (s : Nat) : Nat × Nat :=
  let L := s &&& 255
  let s := s >>> 8
  (s &&& (2 ^ L - 1), s >>> L)

/-- An integer: a sign bit, then a natural number. -/
@[inline] def rdInt (s : Nat) : Int × Nat :=
  let ng := s &&& 1
  let (m, s) := rdNat (s >>> 1)
  (if ng = 1 then -(m : Int) else (m : Int), s)

@[inline] def rdQ (s : Nat) : Q × Nat :=
  let (n, s) := rdInt s
  let (d, s) := rdNat s
  (⟨n, d⟩, s)

/-- A pair of integers. -/
def rdPair (s : Nat) : (Int × Int) × Nat := (((rdInt s).1, (rdInt (rdInt s).2).1), (rdInt (rdInt s).2).2)

/-- `m` pairs of integers. -/
def rdPairs : Nat → Nat → List (Int × Int) × Nat
  | 0, s => ([], s)
  | m + 1, s =>
    let (x, s) := rdInt s
    let (y, s) := rdInt s
    let (r, s) := rdPairs m s
    ((x, y) :: r, s)

/-- `K` atoms `(t_k, m_k)`. -/
def rdAtoms : Nat → Nat → List (Q × Q) × Nat
  | 0, s => ([], s)
  | K + 1, s =>
    let (t, s) := rdQ s
    let (m, s) := rdQ s
    let (r, s) := rdAtoms K s
    ((t, m) :: r, s)

/-! ## Balls of exact data -/

def Q.ball (P : Nat) (q : Q) : Ball := Ball.ofRat P q.n q.d

/-- The dyadic number `n / 2^e` as an exact ball (`e ≤ P`). -/
def dyB (P : Nat) (n : Int) (e : Nat) : Ball := ⟨n * ((2 ^ (P - e) : Nat) : Int), 0⟩

/-- An integer pair as an exact complex ball. -/
def intC (P : Nat) (x : Int × Int) : CBall := ⟨Ball.ofInt P x.1, Ball.ofInt P x.2⟩

/-- `π` from above (units `2^-P`). -/
def piHi (P : Nat) : Nat := ((piB P).hi).toNat

/-- Upper bound of a product of nonnegative quantities (all in units `2^-P`). -/
@[inline] def mulU (P x y : Nat) : Nat := Ball.cdiv (x * y) (2 ^ P)

/-- Upper bound of `e^{π y}` for `0 ≤ y ≤ Y / 2^P` (units `2^-P`). -/
def expPiHi (c : Cfg) (Y : Nat) : Option Nat :=
  (expB c.P c.n (Ball.mul c.P (piB c.P) ⟨(Y : Int), 0⟩)).map fun e => e.hi.toNat

/-- Lower end of the real part of `conj(u) w`. -/
def reConjLo (P : Nat) (u w : CBall) : Int := (CBall.mul P (CBall.conj u) w).re.lo

/-- Upper end of the real part of `conj(u) w`. -/
def reConjHi (P : Nat) (u w : CBall) : Int := (CBall.mul P (CBall.conj u) w).re.hi

/-! ## Ellipses -/

/-- An ellipse `c + a cos 2πq + i b sin 2πq` (`c` complex) as balls. -/
structure EllB where
  cr : Ball
  ci : Ball
  a : Ball
  b : Ball

def ellOf (P : Nat) (e : Q × Q × Q × Q) : EllB := ⟨e.1.ball P, e.2.1.ball P, e.2.2.1.ball P, e.2.2.2.ball P⟩

/-- The point at `q ∈ U`. -/
def ellPt (c : Cfg) (E : EllB) (U : Ball) : Option CBall :=
  (cosSinTurn c.P c.n c.k U).map fun cs =>
    ⟨Ball.add E.cr (Ball.mul c.P E.a cs.1), Ball.add E.ci (Ball.mul c.P E.b cs.2)⟩

/-- Upper bound (units `2^{-2P}`) of `√(a² sin² 2πq + b² cos² 2πq)` (`= |z'(q)| / 2π`) for `q ∈ U`. -/
def ellSp (c : Cfg) (E : EllB) (U : Ball) : Option Nat :=
  (cosSinTurnC c.P c.n c.k U).map fun cs =>
    sqrtHi ((E.a.absHi * cs.2.absHi) ^ 2 + (E.b.absHi * cs.1.absHi) ^ 2)

/-- The piece `[n₀, n₁] / 2^e`: midpoint ball, and the ball of the whole piece. -/
def midB (P : Nat) (n0 n1 e : Nat) : Ball := dyB P ((n0 + n1 : Nat) : Int) (e + 1)
def pieceB (P : Nat) (n0 n1 e : Nat) : Ball :=
  ⟨((n0 + n1 : Nat) : Int) * ((2 ^ (P - (e + 1)) : Nat) : Int), (n1 - n0) * 2 ^ (P - (e + 1))⟩

/-- Radius (units `2^-P`) of a disc around the midpoint that contains the arc of the piece:
`ρ = 2π sp (q₁ - q₀) / 2`. -/
def ellRad (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option Nat :=
  (ellSp c E (pieceB c.P n0 n1 e)).map fun sp =>
    Ball.cdiv (piHi c.P * sp * (n1 - n0)) (2 ^ (2 * c.P + e))

/-! ## Bounds for `S` near a point -/

/-- Upper bound of `sup |S'|` on the disc `D(z, ρ)` from `s1 ∋ S'(z)`: `|S'(z)| + ρ (π²/3) e^{π (|Im z| + ρ)}`. -/
def lsLoc (c : Cfg) (z s1 : CBall) (rho : Nat) : Option Nat :=
  (expPiHi c (z.im.absHi + rho)).map fun eY =>
    normHi s1 + Ball.cdiv (piHi c.P ^ 2 * eY * rho) (3 * 2 ^ (3 * c.P))

/-! ## Bounds in `t` -/

/-- Per point `ζ`: the steps `(K_h(ζ), K_{-h}(ζ))` for `h = 2^{-2}, …, 2^{-D-1}` (from the deepest by squaring),
`w = -2πiζ`, and `mζ ≥ |w|² e^{2π |Im ζ| / 32}`. -/
structure PtT where
  st : List (CBall × CBall)
  w : CBall
  mz : Nat

/-- Squarings: `sqChain P j x acc = [x^(2^j), …, x², x] ++ acc` (componentwise squares of the pair). -/
def sqChain (P : Nat) : Nat → CBall × CBall → List (CBall × CBall) → List (CBall × CBall)
  | 0, x, acc => x :: acc
  | j + 1, x, acc => sqChain P j (CBall.mul P x.1 x.1, CBall.mul P x.2 x.2) (x :: acc)

/-- Upper bound of `π²` (units `2^-P`). -/
def piSqHi (P : Nat) : Nat := Ball.cdiv (piHi P ^ 2) (2 ^ P)

/-- The table of a point (`D ≥ 1` levels). -/
def ptT (c : Cfg) (D : Nat) (z : CBall) : Option PtT :=
  let h := dyB c.P 1 (D + 1)
  (ckt c h z).bind fun kp => (ckt c (Ball.neg h) z).bind fun km =>
    (expPiHi c (Ball.cdiv z.im.absHi 16)).map fun f0 =>
      let w : CBall := ⟨Ball.mulInt 2 (Ball.mul c.P (piB c.P) z.im),
        Ball.neg (Ball.mulInt 2 (Ball.mul c.P (piB c.P) z.re))⟩
      let nz := normHi z
      ⟨sqChain c.P (D - 1) (kp, km) [], w, mulU c.P (4 * mulU c.P (piSqHi c.P) (mulU c.P nz nz)) f0⟩

/-- A term `Re(c K_t(ζ))` at the current cell: `W = c K_{t_c}(ζ)`, `w = -2πiζ`, the remaining steps, `mζ`. -/
structure TermS where
  W : CBall
  w : CBall
  st : List (CBall × CBall)
  m2 : Nat

/-- The term of coefficient `cf` at the point with table `T`, at the root cell `t_c = 0` (`K_0 = 1`). -/
def termOf (cf : CBall) (T : PtT) : TermS := ⟨cf, T.w, T.st, T.mz⟩

/-- Real part of a product (two real multiplications). -/
@[inline] def reMul (P : Nat) (a b : CBall) : Ball := Ball.sub (Ball.mul P a.re b.re) (Ball.mul P a.im b.im)

/-- The value and the derivative of `Σ Re(c K_t(ζ))` at the centre, and `Σ |c K_{t_c}(ζ)| mζ`. -/
def sumTerms (P : Nat) : List TermS → Ball × Ball × Nat
  | [] => (⟨0, 0⟩, ⟨0, 0⟩, 0)
  | T :: ts =>
    let (f, f1, m) := sumTerms P ts
    (Ball.add T.W.re f, Ball.add (reMul P T.W T.w) f1, mulU P (T.W.re.absHi + T.W.im.absHi) T.m2 + m)

/-- The cell `[t_c - 2^{-e}, t_c + 2^{-e}]` (`e ≥ 5`) is accepted:
`f(t_c) + 2^{-e} |f'(t_c)| + 2^{-2e} M₂ / 2 < target`. -/
def cellOK (P : Nat) (ts : List TermS) (e : Nat) (target : Int) : Bool :=
  let (f, f1, m) := sumTerms P ts
  decide (5 ≤ e) &&
    decide (f.hi + (Ball.cdiv f1.absHi (2 ^ e) : Nat) + (Ball.cdiv m (2 ^ (2 * e + 1)) : Nat) < target)

/-- Descend to the child `t_c - h` (`down = true`) or `t_c + h`. -/
def stepT (P : Nat) (down : Bool) (T : TermS) : TermS :=
  match T.st with
  | [] => T
  | (kp, km) :: rest => { T with W := CBall.mul P T.W (if down then km else kp), st := rest }

/-- Adaptive cells: check the cell (unless `skip > 0`), else split; `fuel` bounds the depth. -/
def cells (P : Nat) (target : Int) : Nat → Nat → Nat → List TermS → Bool
  | 0, _, _, _ => false
  | fuel + 1, skip, e, ts =>
    (skip == 0 && cellOK P ts e target) ||
      (cells P target fuel (skip - 1) (e + 1) (ts.map (stepT P true)) &&
       cells P target fuel (skip - 1) (e + 1) (ts.map (stepT P false)))

/-- `Σ Re(c K_t(ζ)) < target` for all `t ∈ [-1/2, 1/2]`: root cell `t_c = 0`, radius `1/2`, 16 cells first. -/
def tbound (P D : Nat) (ts : List TermS) (target : Int) : Bool := cells P target (D + 1) 4 1 ts

/-! ## Pieces of ellipses -/

/-- The data of a piece `[n₀, n₁] / 2^e` of an ellipse: the midpoint ball `z`, the disc radius `ρ`, `S(z)`, `S'(z)`,
`sup |S'|` on the disc, and `e^{π (|Im z| + ρ)}`. -/
structure PieceD where
  z : CBall
  rho : Nat
  sz : CBall
  s1 : CBall
  ls : Nat
  eY : Nat

def pieceD (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option PieceD :=
  (ellPt c E (midB c.P n0 n1 e)).bind fun z =>
  (ellRad c E n0 n1 e).bind fun rho =>
  (cSS1 c z).bind fun ss =>
  (lsLoc c z ss.2 rho).bind fun ls =>
  (expPiHi c (z.im.absHi + rho)).map fun eY => ⟨z, rho, ss.1, ss.2, ls, eY⟩

/-- Lower bound of `Re(ū S)` on the disc of the piece. -/
def aLow (P : Nat) (u : CBall) (pd : PieceD) : Int :=
  reConjLo P u pd.sz - (mulU P (mulU P (normHi u) pd.rho) pd.ls : Nat)

/-- Upper bound of the change of `Re(ū K_t)` over the disc of the piece. -/
def dPof (P : Nat) (u : CBall) (pd : PieceD) : Nat := mulU P (mulU P (normHi u) pd.rho) (mulU P (piHi P) pd.eY)

/-- `⌊a / τ⌋ - dP` for `τ = tn / td` (`a > 0`). -/
def tgt (tn td : Nat) (a : Int) (dP : Nat) : Int := ((a.toNat * td / tn : Nat) : Int) - dP

/-! ## Type E arcs -/

def ePieceOK (g : Glob) (u : CBall) (pd : PieceD) (T : PtT) : Bool :=
  decide (0 < aLow g.P u pd) &&
    tbound g.P g.D [termOf (CBall.conj u) T] (tgt g.tau.n.toNat g.tau.d (aLow g.P u pd) (dPof g.P u pd))

/-- The E condition on the piece `[n₀, n₁] / 2^e` of `T₁`. -/
def checkEPiece (g : Glob) (T1 : EllB) (u : CBall) (n0 n1 e : Nat) : Bool :=
  (pieceD g.cfg T1 n0 n1 e).any fun pd => (ptT g.cfg g.D pd.z).any fun T => ePieceOK g u pd T

/-- Bisection of an E arc. -/
def checkE (g : Glob) (T1 : EllB) (u : CBall) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkEPiece g T1 u n0 n1 e
  | fuel + 1, n0, n1, e => checkEPiece g T1 u n0 n1 e ||
      (checkE g T1 u fuel (2 * n0) (n0 + n1) (e + 1) && checkE g T1 u fuel (n0 + n1) (2 * n1) (e + 1))

/-! ## The crossing radius (Lemma 6.5) -/

/-- `d ≥ |z(s) - z_c|` on the arc. -/
def dOf (P ES : Nat) (sp s0 s1 sc : Nat) : Nat :=
  Ball.cdiv (2 * piHi P * sp * max (s1 - sc) (sc - s0)) (2 ^ (2 * P + ES))

/-- `m_S ≤ |S|` on the arc. -/
def mSOf (P : Nat) (Sc : CBall) (d L : Nat) : Int := (normLo Sc : Int) - (mulU P d L : Nat)

/-- `r = d (π τ e^{πY} + σ_max L)` with `σ_max = τ e^{πY} / m_S`. -/
def rOf (P tn td d L eY : Nat) (mS : Int) : Nat :=
  mulU P d (mulU P (piHi P) (mulU P (Ball.cdiv (tn * 2 ^ P) td) eY) +
    mulU P (Ball.cdiv (tn * eY * 2 ^ P) (td * mS.toNat)) L)

/-- `r_τ` (units `2^-P`) of Lemma 6.5 on the disc `D(z_c, d)` for the arc `[s₀, s₁]` (`s = n / 2^ES`) with centre
`z_c = z(s_c)`, `S_c ∋ S(z_c)`, `S1c ∋ S'(z_c)`, `τ = tn / td`. -/
def rDisc (g : Glob) (T1 : EllB) (tn td : Nat) (s0 s1 sc : Nat) (zc Sc S1c : CBall) : Option Nat :=
  (ellSp g.cfg T1 (pieceB g.P s0 s1 g.ES)).bind fun sp =>
  (lsLoc g.cfg zc S1c (dOf g.P g.ES sp s0 s1 sc)).bind fun L =>
  if 0 < mSOf g.P Sc (dOf g.P g.ES sp s0 s1 sc) L then
    (expPiHi g.cfg (zc.im.absHi + dOf g.P g.ES sp s0 s1 sc)).map fun eY =>
      rOf g.P tn td (dOf g.P g.ES sp s0 s1 sc) L eY (mSOf g.P Sc (dOf g.P g.ES sp s0 s1 sc) L)
  else none

/-- The crossing radius used by the checker: the larger of the proved radius `rDisc` and a proposed value `rX` from
the data (the certificate generator's radius); any number above `rDisc` is again a valid radius. -/
def rBound (g : Glob) (T1 : EllB) (tn td : Nat) (s0 s1 sc : Nat) (zc Sc S1c : CBall) (rX : Nat) : Option Nat :=
  (rDisc g T1 tn td s0 s1 sc zc Sc S1c).map fun r1 => max r1 rX

/-! ## Boxes of the pinned values -/

abbrev Box4 := Ball × Ball × Ball × Ball

/-- A box of the tree for the pin of radius `R`: `(d, i, k)` is
`[R(2i - 2^d)/2^d, R(2i + 2 - 2^d)/2^d] × [R(2k - 2^d)/2^d, R(2k + 2 - 2^d)/2^d]`. -/
def boxB (P : Nat) (R : Q) (d i k : Nat) : Box4 :=
  (Ball.ofRat P (R.n * (2 * (i : Int) - 2 ^ d)) (R.d * 2 ^ d),
   Ball.ofRat P (R.n * (2 * (i : Int) + 2 - 2 ^ d)) (R.d * 2 ^ d),
   Ball.ofRat P (R.n * (2 * (k : Int) - 2 ^ d)) (R.d * 2 ^ d),
   Ball.ofRat P (R.n * (2 * (k : Int) + 2 - 2 ^ d)) (R.d * 2 ^ d))

/-- Lower and upper ends of `Re(ȳ x) = y_r x_r + y_i x_i` over a box (`y` an integer pair). -/
def boxLo (y : Int × Int) (B : Box4) : Int :=
  (Ball.add (Ball.mulInt y.1 (if 0 ≤ y.1 then B.1 else B.2.1))
    (Ball.mulInt y.2 (if 0 ≤ y.2 then B.2.2.1 else B.2.2.2))).lo
def boxHi (y : Int × Int) (B : Box4) : Int :=
  (Ball.add (Ball.mulInt y.1 (if 0 ≤ y.1 then B.2.1 else B.1))
    (Ball.mulInt y.2 (if 0 ≤ y.2 then B.2.2.2 else B.2.2.1))).hi

/-- `w ∈ B` for a complex ball `w` (certainly). -/
def inBox (w : CBall) (B : Box4) : Bool :=
  decide (B.1.hi ≤ w.re.lo) && decide (w.re.hi ≤ B.2.1.lo) && decide (B.2.2.1.hi ≤ w.im.lo) &&
    decide (w.im.hi ≤ B.2.2.2.lo)

/-! ## Arc context -/

/-- Per H arc: `T₁`, the arc, `z_c`, `S(z_c)`, `S'(z_c)`, the table of `z_c`, `r_τ`, and per pin its ball, table
and radius. -/
structure ACtx where
  E1 : EllB
  s0 : Nat
  s1 : Nat
  sc : Nat
  zc : CBall
  Sc : CBall
  S1c : CBall
  zT : PtT
  r : Nat
  pins : List (CBall × PtT × Q)

/-- The boxes of the pins as balls. -/
def pinBoxes (P : Nat) : List (CBall × PtT × Q) → List (Nat × Nat × Nat) → List Box4
  | p :: ps, (d, i, k) :: bs => boxB P p.2.2 d i k :: pinBoxes P ps bs
  | _, _ => []

/-- Terms `Re(c_j K_t(p_j))` with `c_j = ± conj(y_j)` for the nonzero multipliers. -/
def yTerms (P : Nat) (neg : Bool) : List (CBall × PtT × Q) → List (Int × Int) → List TermS
  | p :: ps, y :: ys =>
    if y.1 = 0 ∧ y.2 = 0 then yTerms P neg ps ys
    else termOf (if neg then CBall.neg (CBall.conj (intC P y)) else CBall.conj (intC P y)) p.2.1 :: yTerms P neg ps ys
  | _, _ => []

/-- `Σ_j` of the box bounds. -/
def sumBox (hi : Bool) : List Box4 → List (Int × Int) → Int
  | B :: bs, y :: ys => (if hi then boxHi y B else boxLo y B) + sumBox hi bs ys
  | _, _ => 0

/-! ## Exclusion leaves (Lemma 6.4(a)) -/

/-- `Re(v̄ S(z_c)) - |v| r + Σ_j min_{Q_j} Re(ȳ_j x)` (lower bound). -/
def lbE (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) : Int :=
  reConjLo g.P (intC g.P v) A.Sc - (mulU g.P (normHi (intC g.P v)) A.r : Nat) + sumBox false B ys

def exclOK (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) : Bool :=
  (decide (0 ≤ reConjLo g.P (intC g.P v) A.Sc) || v == (0, 0)) && decide (0 < lbE g A B v ys) &&
    tbound g.P g.D (termOf (CBall.conj (intC g.P v)) A.zT :: yTerms g.P false A.pins ys)
      ((((lbE g A B v ys).toNat * g.tau.d / g.tau.n.toNat : Nat) : Int))

def checkExcl (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) : Bool :=
  exclOK g A (pinBoxes g.P A.pins bx) (rdPair dat).1 (rdPairs A.pins.length (rdPair dat).2).1

/-! ## Witness leaves: tile arcs (Lemma 6.4(b)) -/

/-- `Re(ū S(p)) - Re(v̄ S(z_c)) - |v| r' - Σ_j max_{Q_j} Re(ȳ_j x)` on the disc of the piece (lower bound). -/
def aTA (g : Glob) (A : ACtx) (r' : Nat) (u v : CBall) (hiY : Int) (pd : PieceD) : Int :=
  aLow g.P u pd - reConjHi g.P v A.Sc - (mulU g.P (normHi v) r' : Nat) - hiY

def taPieceOK (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : CBall) (yts : List TermS) (hiY : Int) (pd : PieceD)
    (T : PtT) : Bool :=
  decide (0 < aTA g A r' u v hiY pd) &&
    tbound g.P g.D (termOf (CBall.conj u) T :: termOf (CBall.neg (CBall.conj v)) A.zT :: yts)
      (tgt tn td (aTA g A r' u v hiY pd) (dPof g.P u pd))

/-- The tile-arc condition on the piece `[n₀, n₁] / 2^e` of the tile `E`. -/
def checkTAPiece (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : CBall) (yts : List TermS)
    (hiY : Int) (n0 n1 e : Nat) : Bool :=
  (pieceD g.cfg E n0 n1 e).any fun pd => (ptT g.cfg g.D pd.z).any fun T => taPieceOK g A r' tn td u v yts hiY pd T

def checkTA (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : CBall) (yts : List TermS)
    (hiY : Int) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkTAPiece g A E r' tn td u v yts hiY n0 n1 e
  | fuel + 1, n0, n1, e => checkTAPiece g A E r' tn td u v yts hiY n0 n1 e ||
      (checkTA g A E r' tn td u v yts hiY fuel (2 * n0) (n0 + n1) (e + 1) &&
       checkTA g A E r' tn td u v yts hiY fuel (n0 + n1) (2 * n1) (e + 1))

/-- One tile-arc record: `q₁`, `u`, `v`, `y_1 … y_m`, and the rest of the data. -/
def rdTA (m s : Nat) : Nat × (Int × Int) × (Int × Int) × List (Int × Int) × Nat :=
  ((rdNat s).1, (rdPair (rdNat s).2).1, (rdPair (rdPair (rdNat s).2).2).1,
   (rdPairs m (rdPair (rdPair (rdNat s).2).2).2).1, (rdPairs m (rdPair (rdPair (rdNat s).2).2).2).2)

/-- The checks of one tile arc `[q₀, q₁]`. -/
def taOK (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (q0 q1 : Nat) (u v : Int × Int)
    (ys : List (Int × Int)) : Bool :=
  decide (q0 < q1) && decide (q1 ≤ 2 ^ g.EQ) && (decide (reConjHi g.P (intC g.P v) A.Sc ≤ 0) || v == (0, 0)) &&
    checkTA g A E r' tn td (intC g.P u) (intC g.P v) (yTerms g.P true A.pins ys) (sumBox true B ys) g.dT q0 q1 g.EQ

/-- The tile arcs `[q₀, q₁], [q₁, q₂], …` (`q = n / 2^EQ`, from `q₀` to `1`), `N` records left. -/
def checkTAs (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | N + 1, q0, s =>
    taOK g A E r' tn td B q0 (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.1 (rdTA A.pins.length s).2.2.1
        (rdTA A.pins.length s).2.2.2.1 &&
      ((rdTA A.pins.length s).1 == 2 ^ g.EQ ||
        checkTAs g A E r' tn td B N (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.2.2.2)

/-! ## Witness measures -/

/-- `Σ m_k K_{t_k}(z)`. -/
def sumK (c : Cfg) (z : CBall) : List (Q × Q) → Option CBall
  | [] => some ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
  | (t, m) :: as => (ckt c (t.ball c.P) z).bind fun k => (sumK c z as).map fun s =>
      CBall.add (CBall.mulR c.P (m.ball c.P) k) s

/-- Exact rational checks: `m_k ≥ 0`, `|t_k| ≤ 1/2`, denominators positive; returns `Σ m_k` as `(num, den)`. -/
def atomsOK : List (Q × Q) → Option (Int × Nat)
  | [] => some (0, 1)
  | (t, m) :: as =>
    if 0 < t.d ∧ 2 * t.n.natAbs ≤ t.d ∧ 0 < m.d ∧ 0 ≤ m.n then
      (atomsOK as).map fun s => (m.n * s.2 + s.1 * m.d, m.d * s.2)
    else none

/-! ## Winding numbers (half-plane labels) -/

def jmpI (h h' : Nat) : Int := if h = 3 ∧ h' = 0 then 1 else if h = 0 ∧ h' = 3 then -1 else 0

/-- A half-plane label of the ball `gm` with margin `thr`. -/
def label (gm : CBall) (thr : Int) : Option Nat :=
  if thr < gm.re.lo then some 0 else if thr < gm.im.lo then some 1
  else if gm.re.hi + thr < 0 then some 2 else if gm.im.hi + thr < 0 then some 3 else none

/-- A label `h` with `Re(g (-i)^h) > 0` on the piece, `g = S - Σ m_k K_{t_k}`; `mSum ≥ Σ m_k` (units). -/
def windPiece (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (n0 n1 e : Nat) : Option Nat :=
  (pieceD c E n0 n1 e).bind fun pd => (sumK c pd.z as).bind fun wk =>
    label (CBall.sub pd.sz wk) ((mulU c.P (pd.ls + mulU c.P mSum (mulU c.P (piHi c.P) pd.eY)) pd.rho : Nat))

/-- Labelled pieces of `[n₀, n₁] / 2^e`: first label, last label, internal jumps. -/
def wind (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) : Nat → Nat → Nat → Nat → Nat →
    Option (Nat × Nat × Int)
  | 0, _, _, _, _ => none
  | fuel + 1, skip, n0, n1, e =>
    ((if skip = 0 then windPiece c E as mSum n0 n1 e else none).map fun h => (h, h, (0 : Int))).orElse fun _ =>
      (wind c E as mSum fuel (skip - 1) (2 * n0) (n0 + n1) (e + 1)).bind fun r1 =>
        (wind c E as mSum fuel (skip - 1) (n0 + n1) (2 * n1) (e + 1)).map fun r2 =>
          (r1.1, r2.2.1, r1.2.2 + r2.2.2 + jmpI r1.2.1 r2.1)

/-- The winding number along the whole ellipse is odd (64 initial pieces). -/
def windOdd (g : Glob) (E : EllB) (as : List (Q × Q)) (mSum : Nat) : Bool :=
  (wind g.cfg E as mSum (g.dW + 1) 6 0 1 0).any fun r => (r.2.2 + jmpI r.2.1 r.1) % 2 == 1

/-! ## Witness leaves -/

def tileOf (g : Glob) (i : Nat) : Option EllB := (g.tiles[i]?).map (ellOf g.P)

/-- The decoded witness leaf: tile index, `τ'`, proposed radius `rX` for `τ'`, `σ`, atoms, number of tile arcs, the
tile-arc data. -/
structure WitD where
  ti : Nat
  tw : Q
  rX : Nat
  sg : Q
  as : List (Q × Q)
  N : Nat
  dat : Nat

def rdWit (dat : Nat) : WitD :=
  ⟨(rdNat dat).1, (rdQ (rdNat dat).2).1, (rdNat (rdQ (rdNat dat).2).2).1,
   (rdQ (rdNat (rdQ (rdNat dat).2).2).2).1,
   (rdAtoms (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).1 (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).2).1,
   (rdNat (rdAtoms (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).1
     (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).2).2).1,
   (rdNat (rdAtoms (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).1
     (rdNat (rdQ (rdNat (rdQ (rdNat dat).2).2).2).2).2).2).2⟩

/-- `ŵ(p_j) ∈ Q_j` for all pins. -/
def pinsIn (c : Cfg) (as : List (Q × Q)) : List (CBall × PtT × Q) → List Box4 → Bool
  | p :: ps, B :: bs => ((sumK c p.1 as).any fun w => inBox w B) && pinsIn c as ps bs
  | _, _ => true

/-- The exact checks: `τ'> 0`, `τ ≤ τ'`, `Σ m_k ≤ τ'`, `σ ≥ 1`. -/
def witExact (g : Glob) (w : WitD) (mn : Int) (md : Nat) : Bool :=
  decide (0 < w.tw.n) && decide (0 < w.tw.d) && decide (g.tau.n * w.tw.d ≤ w.tw.n * g.tau.d) &&
    decide (mn * w.tw.d ≤ w.tw.n * md) && decide (0 < w.sg.d) && decide ((w.sg.d : Int) ≤ w.sg.n)

/-- The ball checks with `r'`: `r ≤ r'`, the crossing disc, the pins, the tile arcs, the winding number. -/
def witBall (g : Glob) (A : ACtx) (B : List Box4) (E : EllB) (w : WitD) (mn : Int) (md r' : Nat) (wz : CBall) : Bool :=
  decide (A.r ≤ r') && decide (normHi (CBall.sub wz (CBall.mulR g.P (w.sg.ball g.P) A.Sc)) ≤ r') &&
    pinsIn g.cfg w.as A.pins B && checkTAs g A E r' w.tw.n.toNat w.tw.d B w.N 0 w.dat &&
    windOdd g E w.as (Ball.cdiv (mn.toNat * 2 ^ g.P) md)

/-- The checks of a decoded witness leaf. -/
def witOK (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) : Bool :=
  (tileOf g w.ti).any fun E => (atomsOK w.as).any fun mm =>
    witExact g w mm.1 mm.2 &&
      ((rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX).any fun r' =>
        (sumK g.cfg A.zc w.as).any fun wz => witBall g A (pinBoxes g.P A.pins bx) E w mm.1 mm.2 r' wz)

def checkWit (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) : Bool := witOK g A bx (rdWit dat)

/-! ## Type H arcs -/

/-- The four children of the box `(d, i, k)`. -/
def kid (b : Nat × Nat × Nat) (n : Nat) : Nat × Nat × Nat :=
  (b.1 + 1, 2 * b.2.1 + n % 2, 2 * b.2.2 + n / 2)

/-- The leaf tree; `bx` are the boxes `(d, i, k)` of the pins. -/
def walk (g : Glob) (A : ACtx) : Tree → List (Nat × Nat × Nat) → Bool
  | .excl dat, bx => checkExcl g A bx dat
  | .wit dat, bx => checkWit g A bx dat
  | .split j c0 c1 c2 c3, bx =>
    decide (j < bx.length) &&
      walk g A c0 (bx.set j (kid (bx.getD j (0, 0, 0)) 0)) && walk g A c1 (bx.set j (kid (bx.getD j (0, 0, 0)) 1)) &&
      walk g A c2 (bx.set j (kid (bx.getD j (0, 0, 0)) 2)) && walk g A c3 (bx.set j (kid (bx.getD j (0, 0, 0)) 3))

/-- `R_j ≥ τ e^{π |Im p_j|}` (from the balls). -/
def pinROK (g : Glob) (p : CBall) (R : Q) : Bool :=
  (expPiHi g.cfg p.im.absHi).any fun eY => decide (0 < R.d) &&
    decide ((mulU g.P (Ball.cdiv (g.tau.n.toNat * 2 ^ g.P) g.tau.d) eY : Int) ≤ (R.ball g.P).lo)

/-- The ellipse `T₁` as balls. -/
def T1B (g : Glob) : EllB := ellOf g.P (g.c, ⟨0, 1⟩, g.a, g.b)

def pinBall (P : Nat) (p : Q × Q) : CBall := ⟨p.1.ball P, p.2.ball P⟩

/-- The arc context, if all its enclosures exist. -/
def arcCtx (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) : Option ACtx :=
  (ellPt g.cfg (T1B g) (dyB g.P sc g.ES)).bind fun zc =>
  (cSS1 g.cfg zc).bind fun ss =>
  (ptT g.cfg g.D zc).bind fun zT =>
  (rBound g (T1B g) g.tau.n.toNat g.tau.d s0 s1 sc zc ss.1 ss.2 rX).bind fun r =>
  ((pins.map (pinBall g.P)).mapM (ptT g.cfg g.D)).map fun pts =>
    ⟨T1B g, s0, s1, sc, zc, ss.1, ss.2, zT, r, (pins.map (pinBall g.P)).zip (pts.zip Rs)⟩

/-- The header checks of an H arc. -/
def hHead (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) : Bool :=
  decide (s0 ≤ sc) && decide (sc ≤ s1) && decide (s0 < s1) && decide (pins.length = Rs.length) &&
    pins.all (fun p => decide (0 < p.1.d) && decide (0 < p.2.d)) &&
    ((pins.map (pinBall g.P)).zip Rs).all (fun x => pinROK g x.1 x.2)

def checkH (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : Tree) : Bool :=
  hHead g s0 s1 sc pins Rs && (arcCtx g s0 s1 sc pins Rs rX).any fun A => walk g A t (pins.map fun _ => (0, 0, 0))

def checkArc (g : Glob) : Arc → Bool
  | .E s0 s1 ur ui => decide (s0 < s1) && checkE g (T1B g) (intC g.P (ur, ui)) g.dE s0 s1 g.ES
  | .H s0 s1 sc pins Rs rX t => checkH g s0 s1 sc pins Rs rX t

/-! ## Global conditions -/

/-- `τ`, `T₁`, the tiles and the parameters. -/
def globParams (g : Glob) : Bool :=
  decide (0 < g.tau.n) && decide ((g.tau.n : Int) < g.tau.d) && decide (0 < g.c.d) && decide (0 < g.a.d) &&
    decide (0 < g.b.d) && decide (0 < g.a.n) && decide (0 < g.b.n) && decide (1 ≤ g.D) &&
    decide (g.ES + g.dE + 1 ≤ g.P) && decide (g.EQ + g.dT + 1 ≤ g.P) && decide (g.dW + 2 ≤ g.P) &&
    decide (g.D + 1 ≤ g.P) &&
    g.tiles.all (fun e => decide (0 < e.1.d) && decide (0 < e.2.1.d) && decide (0 < e.2.2.1.d) &&
      decide (0 < e.2.2.2.d) && decide (0 < e.2.2.1.n) && decide (0 < e.2.2.2.n))

/-- The parameters and the odd winding number of `S` along `T₁`. -/
def checkGlob (g : Glob) : Bool := globParams g && windOdd g (T1B g) [] 0

/-- The arcs `[s₀, s₁]` cover `[0, 1]` consecutively. -/
def coverOK (g : Glob) : Nat → List (Nat × Nat) → Bool
  | _, [] => false
  | x, [(a, b)] => x == a && b == 2 ^ g.ES
  | x, (a, b) :: rest => x == a && coverOK g b rest

def Arc.s0 : Arc → Nat
  | .E s0 _ _ _ => s0
  | .H s0 _ _ _ _ _ _ => s0

def Arc.s1 : Arc → Nat
  | .E _ s1 _ _ => s1
  | .H _ s1 _ _ _ _ _ => s1

end C64Chk
