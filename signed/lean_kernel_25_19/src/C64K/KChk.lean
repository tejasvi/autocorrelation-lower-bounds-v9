import C64Core.Check
import C64K.KNum

/-!
# The c64 checker on sign-magnitude balls (kernel layer, core Lean only)

`C64KChk` mirrors `C64Chk` (`C64Core/Check.lean`, checker v5'') function by function on `KIval.KBall` / `KNum.KCBall`.  The data
types (`C64Chk.Q`, `Tree`, `Arc`, `Glob`) and the data-only functions (decoding `rd*`, `atomsOK`, `witExact`,
`globParams`, `coverOK`, `kid`, `jmpI`) are those of `C64Chk`; integers of the data enter the ball arithmetic in
sign-magnitude form (`negI`, `Int.natAbs`), computed integers are signed pairs `SI`.  Every ball is the image of the
corresponding `C64Chk` ball under `KBall.toBall`, so `checkArcK g a = checkArc g a` (`C64K.KChkSim`).

Kernel-oriented style: `Nat` primitives, branching by `cond`, projections instead of matches on computed values
(except the list recursions of the original).
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

/-! ## Signed integers -/

/-- The signed integer `(-1)^s m`. -/
structure SI where
  s : Bool
  m : Nat
deriving Repr, Inhabited

namespace SI

@[inline] def ofNat (n : Nat) : SI := ⟨false, n⟩

/-- `a + b` (by `KBall.sadd`). -/
@[inline] def add (a b : SI) : SI := let k := sadd a.s a.m b.s b.m 0; ⟨k.s, k.m⟩

/-- `a - b`. -/
@[inline] def sub (a b : SI) : SI := let k := sadd a.s a.m (cond b.s false true) b.m 0; ⟨k.s, k.m⟩

/-- `a ≤ b`. -/
@[inline] def le (a b : SI) : Bool := sle a.s a.m b.s b.m

/-- `a < b`. -/
@[inline] def lt (a b : SI) : Bool := cond (sle b.s b.m a.s a.m) false true

/-- `Int.toNat`. -/
@[inline] def toNat (a : SI) : Nat := cond a.s 0 a.m

/-- `a = 0`. -/
@[inline] def isZero (a : SI) : Bool := Nat.beq a.m 0

/-- `0 ≤ a`. -/
@[inline] def nonneg (a : SI) : Bool := cond a.s (Nat.beq a.m 0) true

/-- Product (signs by exclusive or). -/
@[inline] def mul (a b : SI) : SI := ⟨bx a.s b.s, Nat.mul a.m b.m⟩

end SI

/-- The sign of a data integer. -/
def negI : Int → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- A data integer as a signed pair. -/
@[inline] def sI (n : Int) : SI := ⟨negI n, n.natAbs⟩

/-- Lower end `(-1)^s m - r` and upper end `(-1)^s m + r` of a ball. -/
@[inline] def loS (a : KBall) : SI := let k := sadd a.s a.m true a.r 0; ⟨k.s, k.m⟩
@[inline] def hiS (a : KBall) : SI := let k := sadd a.s a.m false a.r 0; ⟨k.s, k.m⟩

/-- `Int.toNat` of the upper end. -/
@[inline] def hiNat (a : KBall) : Nat := SI.toNat (hiS a)

/-! ## Balls of exact data -/

def qBall (P : Nat) (q : Q) : KBall := KBall.ofRat P (negI q.n) q.n.natAbs q.d

/-- The dyadic number `n / 2^e` (`n ≥ 0`) as an exact ball. -/
def dyB (P n e : Nat) : KBall := ⟨false, Nat.mul n (Nat.pow 2 (Nat.sub P e)), 0⟩

/-- An integer pair as an exact complex ball. -/
def intC (P : Nat) (x : Int × Int) : KCBall := ⟨KBall.ofInt P (negI x.1) x.1.natAbs, KBall.ofInt P (negI x.2) x.2.natAbs⟩

def piHi (P : Nat) : Nat := hiNat (piB P)

@[inline] def mulU (P x y : Nat) : Nat := KBall.cdiv (Nat.mul x y) (Nat.pow 2 P)

def expPiHi (c : Cfg) (Y : Nat) : Option Nat :=
  (expB c.P c.n (KBall.mul c.P (piB c.P) ⟨false, Y, 0⟩)).map hiNat

def reConjLo (P : Nat) (u w : KCBall) : SI := loS (KCBall.mul P (KCBall.conj u) w).re

def reConjHi (P : Nat) (u w : KCBall) : SI := hiS (KCBall.mul P (KCBall.conj u) w).re

/-! ## Ellipses -/

structure EllB where
  cr : KBall
  ci : KBall
  a : KBall
  b : KBall

def ellOf (P : Nat) (e : Q × Q × Q × Q) : EllB := ⟨qBall P e.1, qBall P e.2.1, qBall P e.2.2.1, qBall P e.2.2.2⟩

def ellPt (c : Cfg) (E : EllB) (U : KBall) : Option KCBall :=
  (cosSinTurn c.P c.n c.k U).map fun cs =>
    ⟨KBall.add E.cr (KBall.mul c.P E.a cs.1), KBall.add E.ci (KBall.mul c.P E.b cs.2)⟩

def ellSp (c : Cfg) (E : EllB) (U : KBall) : Option Nat :=
  (cosSinTurnC c.P c.n c.k U).map fun cs =>
    sqrtHi (Nat.add (Nat.pow (Nat.mul (absHi E.a) (absHi cs.2)) 2) (Nat.pow (Nat.mul (absHi E.b) (absHi cs.1)) 2))

def midB (P n0 n1 e : Nat) : KBall := dyB P (Nat.add n0 n1) (Nat.add e 1)

def pieceB (P n0 n1 e : Nat) : KBall :=
  ⟨false, Nat.mul (Nat.add n0 n1) (Nat.pow 2 (Nat.sub P (Nat.add e 1))),
    Nat.mul (Nat.sub n1 n0) (Nat.pow 2 (Nat.sub P (Nat.add e 1)))⟩

def ellRad (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option Nat :=
  (ellSp c E (pieceB c.P n0 n1 e)).map fun sp =>
    KBall.cdiv (Nat.mul (Nat.mul (piHi c.P) sp) (Nat.sub n1 n0)) (Nat.pow 2 (Nat.add (Nat.mul 2 c.P) e))

def lsLoc (c : Cfg) (z s1 : KCBall) (rho : Nat) : Option Nat :=
  (expPiHi c (Nat.add (absHi z.im) rho)).map fun eY =>
    Nat.add (normHi s1)
      (KBall.cdiv (Nat.mul (Nat.mul (Nat.pow (piHi c.P) 2) eY) rho) (Nat.mul 3 (Nat.pow 2 (Nat.mul 3 c.P))))

/-! ## Bounds in `t` -/

structure PtT where
  st : List (KCBall × KCBall)
  w : KCBall
  mz : Nat

def sqChain (P : Nat) : Nat → KCBall × KCBall → List (KCBall × KCBall) → List (KCBall × KCBall)
  | 0, x, acc => x :: acc
  | j + 1, x, acc => sqChain P j (KCBall.mul P x.1 x.1, KCBall.mul P x.2 x.2) (x :: acc)

def piSqHi (P : Nat) : Nat := KBall.cdiv (Nat.pow (piHi P) 2) (Nat.pow 2 P)

def ptT (c : Cfg) (D : Nat) (z : KCBall) : Option PtT :=
  let h := dyB c.P 1 (Nat.add D 1)
  (ckt c h z).bind fun kp => (ckt c (KBall.neg h) z).bind fun km =>
    (expPiHi c (KBall.cdiv (absHi z.im) 16)).map fun f0 =>
      let w : KCBall := ⟨KBall.mulInt false 2 (KBall.mul c.P (piB c.P) z.im),
        KBall.neg (KBall.mulInt false 2 (KBall.mul c.P (piB c.P) z.re))⟩
      let nz := normHi z
      ⟨sqChain c.P (Nat.sub D 1) (kp, km) [], w,
        mulU c.P (Nat.mul 4 (mulU c.P (piSqHi c.P) (mulU c.P nz nz))) f0⟩

structure TermS where
  W : KCBall
  w : KCBall
  st : List (KCBall × KCBall)
  m2 : Nat

def termOf (cf : KCBall) (T : PtT) : TermS := ⟨cf, T.w, T.st, T.mz⟩

@[inline] def reMul (P : Nat) (a b : KCBall) : KBall := KBall.sub (KBall.mul P a.re b.re) (KBall.mul P a.im b.im)

def sumTerms (P : Nat) : List TermS → KBall × KBall × Nat
  | [] => (⟨false, 0, 0⟩, ⟨false, 0, 0⟩, 0)
  | T :: ts =>
    let r := sumTerms P ts
    (KBall.add T.W.re r.1, KBall.add (reMul P T.W T.w) r.2.1,
      Nat.add (mulU P (Nat.add (absHi T.W.re) (absHi T.W.im)) T.m2) r.2.2)

def cellOK (P : Nat) (ts : List TermS) (e : Nat) (target : SI) : Bool :=
  let r := sumTerms P ts
  cond (Nat.ble 5 e)
    (SI.lt (SI.add (hiS r.1) (SI.ofNat (Nat.add (KBall.cdiv (absHi r.2.1) (Nat.pow 2 e))
      (KBall.cdiv r.2.2 (Nat.pow 2 (Nat.add (Nat.mul 2 e) 1)))))) target)
    false

def stepT (P : Nat) (down : Bool) (T : TermS) : TermS :=
  match T.st with
  | [] => T
  | (kp, km) :: rest => ⟨KCBall.mul P T.W (cond down km kp), T.w, rest, T.m2⟩

def cells (P : Nat) (target : SI) : Nat → Nat → Nat → List TermS → Bool
  | 0, _, _, _ => false
  | fuel + 1, skip, e, ts =>
    (cond (Nat.beq skip 0) (cellOK P ts e target) false) ||
      (cells P target fuel (Nat.sub skip 1) (Nat.add e 1) (ts.map (stepT P true)) &&
       cells P target fuel (Nat.sub skip 1) (Nat.add e 1) (ts.map (stepT P false)))

def tbound (P D : Nat) (ts : List TermS) (target : SI) : Bool := cells P target (Nat.add D 1) 4 1 ts

/-! ## Pieces of ellipses -/

structure PieceD where
  z : KCBall
  rho : Nat
  sz : KCBall
  s1 : KCBall
  ls : Nat
  eY : Nat

def pieceD (c : Cfg) (E : EllB) (n0 n1 e : Nat) : Option PieceD :=
  (ellPt c E (midB c.P n0 n1 e)).bind fun z =>
  (ellRad c E n0 n1 e).bind fun rho =>
  (cSS1 c z).bind fun ss =>
  (lsLoc c z ss.2 rho).bind fun ls =>
  (expPiHi c (Nat.add (absHi z.im) rho)).map fun eY => ⟨z, rho, ss.1, ss.2, ls, eY⟩

def aLow (P : Nat) (u : KCBall) (pd : PieceD) : SI :=
  SI.sub (reConjLo P u pd.sz) (SI.ofNat (mulU P (mulU P (normHi u) pd.rho) pd.ls))

def dPof (P : Nat) (u : KCBall) (pd : PieceD) : Nat := mulU P (mulU P (normHi u) pd.rho) (mulU P (piHi P) pd.eY)

def tgt (tn td : Nat) (a : SI) (dP : Nat) : SI := SI.sub (SI.ofNat (Nat.div (Nat.mul (SI.toNat a) td) tn)) (SI.ofNat dP)

/-! ## Type E arcs -/

def ePieceOK (g : Glob) (u : KCBall) (pd : PieceD) (T : PtT) : Bool :=
  SI.lt (SI.ofNat 0) (aLow g.P u pd) &&
    tbound g.P g.D [termOf (KCBall.conj u) T] (tgt g.tau.n.toNat g.tau.d (aLow g.P u pd) (dPof g.P u pd))

def checkEPiece (g : Glob) (T1 : EllB) (u : KCBall) (n0 n1 e : Nat) : Bool :=
  (pieceD ⟨g.P, g.n, g.k⟩ T1 n0 n1 e).any fun pd => (ptT ⟨g.P, g.n, g.k⟩ g.D pd.z).any fun T => ePieceOK g u pd T

def checkE (g : Glob) (T1 : EllB) (u : KCBall) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkEPiece g T1 u n0 n1 e
  | fuel + 1, n0, n1, e => checkEPiece g T1 u n0 n1 e ||
      (checkE g T1 u fuel (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1) &&
       checkE g T1 u fuel (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1))

/-! ## The crossing radius -/

@[inline] def nmax (a b : Nat) : Nat := cond (Nat.ble a b) b a

def dOf (P ES : Nat) (sp s0 s1 sc : Nat) : Nat :=
  KBall.cdiv (Nat.mul (Nat.mul (Nat.mul 2 (piHi P)) sp) (nmax (Nat.sub s1 sc) (Nat.sub sc s0)))
    (Nat.pow 2 (Nat.add (Nat.mul 2 P) ES))

def mSOf (P : Nat) (Sc : KCBall) (d L : Nat) : SI := SI.sub (SI.ofNat (normLo Sc)) (SI.ofNat (mulU P d L))

def rOf (P tn td d L eY : Nat) (mS : SI) : Nat :=
  mulU P d (Nat.add (mulU P (piHi P) (mulU P (KBall.cdiv (Nat.mul tn (Nat.pow 2 P)) td) eY))
    (mulU P (KBall.cdiv (Nat.mul (Nat.mul tn eY) (Nat.pow 2 P)) (Nat.mul td (SI.toNat mS))) L))

def rDisc (g : Glob) (T1 : EllB) (tn td : Nat) (s0 s1 sc : Nat) (zc Sc S1c : KCBall) : Option Nat :=
  (ellSp ⟨g.P, g.n, g.k⟩ T1 (pieceB g.P s0 s1 g.ES)).bind fun sp =>
  (lsLoc ⟨g.P, g.n, g.k⟩ zc S1c (dOf g.P g.ES sp s0 s1 sc)).bind fun L =>
  cond (SI.lt (SI.ofNat 0) (mSOf g.P Sc (dOf g.P g.ES sp s0 s1 sc) L))
    ((expPiHi ⟨g.P, g.n, g.k⟩ (Nat.add (absHi zc.im) (dOf g.P g.ES sp s0 s1 sc))).map fun eY =>
      rOf g.P tn td (dOf g.P g.ES sp s0 s1 sc) L eY (mSOf g.P Sc (dOf g.P g.ES sp s0 s1 sc) L))
    none

/-- The crossing radius used by the checker: `max (rDisc ..) rX`. -/
def rBound (g : Glob) (T1 : EllB) (tn td : Nat) (s0 s1 sc : Nat) (zc Sc S1c : KCBall) (rX : Nat) : Option Nat :=
  (rDisc g T1 tn td s0 s1 sc zc Sc S1c).map fun r1 => nmax r1 rX

/-! ## Boxes of the pinned values -/

abbrev Box4 := KBall × KBall × KBall × KBall

/-- `R.n (2 i - 2^d)` as a signed pair. -/
@[inline] def boxNum (R : Q) (a b : Nat) : SI :=
  SI.mul (sI R.n) (cond (Nat.ble b a) ⟨false, Nat.sub a b⟩ ⟨true, Nat.sub b a⟩)

@[inline] def boxEnd (P : Nat) (R : Q) (a b : Nat) : KBall :=
  KBall.ofRat P (boxNum R a b).s (boxNum R a b).m (Nat.mul R.d b)

def boxB (P : Nat) (R : Q) (d i k : Nat) : Box4 :=
  (boxEnd P R (Nat.mul 2 i) (Nat.pow 2 d), boxEnd P R (Nat.add (Nat.mul 2 i) 2) (Nat.pow 2 d),
   boxEnd P R (Nat.mul 2 k) (Nat.pow 2 d), boxEnd P R (Nat.add (Nat.mul 2 k) 2) (Nat.pow 2 d))

def boxLo (y : Int × Int) (B : Box4) : SI :=
  loS (KBall.add (KBall.mulInt (negI y.1) y.1.natAbs (cond (SI.nonneg (sI y.1)) B.1 B.2.1))
    (KBall.mulInt (negI y.2) y.2.natAbs (cond (SI.nonneg (sI y.2)) B.2.2.1 B.2.2.2)))

def boxHi (y : Int × Int) (B : Box4) : SI :=
  hiS (KBall.add (KBall.mulInt (negI y.1) y.1.natAbs (cond (SI.nonneg (sI y.1)) B.2.1 B.1))
    (KBall.mulInt (negI y.2) y.2.natAbs (cond (SI.nonneg (sI y.2)) B.2.2.2 B.2.2.1)))

def inBox (w : KCBall) (B : Box4) : Bool :=
  SI.le (hiS B.1) (loS w.re) && SI.le (hiS w.re) (loS B.2.1) && SI.le (hiS B.2.2.1) (loS w.im) &&
    SI.le (hiS w.im) (loS B.2.2.2)

/-! ## Arc context -/

structure ACtx where
  E1 : EllB
  s0 : Nat
  s1 : Nat
  sc : Nat
  zc : KCBall
  Sc : KCBall
  S1c : KCBall
  zT : PtT
  r : Nat
  pins : List (KCBall × PtT × Q)

def pinBoxes (P : Nat) : List (KCBall × PtT × Q) → List (Nat × Nat × Nat) → List Box4
  | p :: ps, b :: bs => boxB P p.2.2 b.1 b.2.1 b.2.2 :: pinBoxes P ps bs
  | _, _ => []

/-- `a + b` on data integer pairs is `0`. -/
@[inline] def isZ2 (y : Int × Int) : Bool := Nat.beq y.1.natAbs 0 && Nat.beq y.2.natAbs 0

def yTerms (P : Nat) (neg : Bool) : List (KCBall × PtT × Q) → List (Int × Int) → List TermS
  | p :: ps, y :: ys =>
    cond (isZ2 y) (yTerms P neg ps ys)
      (termOf (cond neg (KCBall.neg (KCBall.conj (intC P y))) (KCBall.conj (intC P y))) p.2.1 :: yTerms P neg ps ys)
  | _, _ => []

def sumBox (hi : Bool) : List Box4 → List (Int × Int) → SI
  | B :: bs, y :: ys => SI.add (cond hi (boxHi y B) (boxLo y B)) (sumBox hi bs ys)
  | _, _ => SI.ofNat 0

/-! ## Exclusion leaves -/

def lbE (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) : SI :=
  SI.add (SI.sub (reConjLo g.P (intC g.P v) A.Sc) (SI.ofNat (mulU g.P (normHi (intC g.P v)) A.r))) (sumBox false B ys)

def exclOK (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) : Bool :=
  (SI.nonneg (reConjLo g.P (intC g.P v) A.Sc) || isZ2 v) && SI.lt (SI.ofNat 0) (lbE g A B v ys) &&
    tbound g.P g.D (termOf (KCBall.conj (intC g.P v)) A.zT :: yTerms g.P false A.pins ys)
      (SI.ofNat (Nat.div (Nat.mul (SI.toNat (lbE g A B v ys)) g.tau.d) g.tau.n.toNat))

def checkExcl (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) : Bool :=
  exclOK g A (pinBoxes g.P A.pins bx) (rdPair dat).1 (rdPairs A.pins.length (rdPair dat).2).1

/-! ## Witness leaves: tile arcs -/

def aTA (g : Glob) (A : ACtx) (r' : Nat) (u v : KCBall) (hiY : SI) (pd : PieceD) : SI :=
  SI.sub (SI.sub (SI.sub (aLow g.P u pd) (reConjHi g.P v A.Sc)) (SI.ofNat (mulU g.P (normHi v) r'))) hiY

def taPieceOK (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY : SI) (pd : PieceD)
    (T : PtT) : Bool :=
  SI.lt (SI.ofNat 0) (aTA g A r' u v hiY pd) &&
    tbound g.P g.D (termOf (KCBall.conj u) T :: termOf (KCBall.neg (KCBall.conj v)) A.zT :: yts)
      (tgt tn td (aTA g A r' u v hiY pd) (dPof g.P u pd))

def checkTAPiece (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY : SI) (n0 n1 e : Nat) : Bool :=
  (pieceD ⟨g.P, g.n, g.k⟩ E n0 n1 e).any fun pd =>
    (ptT ⟨g.P, g.n, g.k⟩ g.D pd.z).any fun T => taPieceOK g A r' tn td u v yts hiY pd T

def checkTA (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY : SI) : Nat → Nat → Nat → Nat → Bool
  | 0, n0, n1, e => checkTAPiece g A E r' tn td u v yts hiY n0 n1 e
  | fuel + 1, n0, n1, e => checkTAPiece g A E r' tn td u v yts hiY n0 n1 e ||
      (checkTA g A E r' tn td u v yts hiY fuel (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1) &&
       checkTA g A E r' tn td u v yts hiY fuel (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1))

def taOK (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (q0 q1 : Nat) (u v : Int × Int)
    (ys : List (Int × Int)) : Bool :=
  blt q0 q1 && Nat.ble q1 (Nat.pow 2 g.EQ) && (SI.le (reConjHi g.P (intC g.P v) A.Sc) (SI.ofNat 0) || isZ2 v) &&
    checkTA g A E r' tn td (intC g.P u) (intC g.P v) (yTerms g.P true A.pins ys) (sumBox true B ys) g.dT q0 q1 g.EQ

def checkTAs (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | N + 1, q0, s =>
    taOK g A E r' tn td B q0 (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.1 (rdTA A.pins.length s).2.2.1
        (rdTA A.pins.length s).2.2.2.1 &&
      (Nat.beq (rdTA A.pins.length s).1 (Nat.pow 2 g.EQ) ||
        checkTAs g A E r' tn td B N (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.2.2.2)

/-! ## Witness measures -/

def sumK (c : Cfg) (z : KCBall) : List (Q × Q) → Option KCBall
  | [] => some ⟨⟨false, 0, 0⟩, ⟨false, 0, 0⟩⟩
  | a :: as => (ckt c (qBall c.P a.1) z).bind fun k => (sumK c z as).map fun s =>
      KCBall.add (KCBall.mulR c.P (qBall c.P a.2) k) s

/-! ## Winding numbers -/

def label (gm : KCBall) (thr : Nat) : Option Nat :=
  cond (SI.lt (SI.ofNat thr) (loS gm.re)) (some 0)
    (cond (SI.lt (SI.ofNat thr) (loS gm.im)) (some 1)
      (cond (SI.lt (SI.add (hiS gm.re) (SI.ofNat thr)) (SI.ofNat 0)) (some 2)
        (cond (SI.lt (SI.add (hiS gm.im) (SI.ofNat thr)) (SI.ofNat 0)) (some 3) none)))

def windPiece (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) (n0 n1 e : Nat) : Option Nat :=
  (pieceD c E n0 n1 e).bind fun pd => (sumK c pd.z as).bind fun wk =>
    label (KCBall.sub pd.sz wk) (mulU c.P (Nat.add pd.ls (mulU c.P mSum (mulU c.P (piHi c.P) pd.eY))) pd.rho)

def wind (c : Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) : Nat → Nat → Nat → Nat → Nat →
    Option (Nat × Nat × Int)
  | 0, _, _, _, _ => none
  | fuel + 1, skip, n0, n1, e =>
    ((cond (Nat.beq skip 0) (windPiece c E as mSum n0 n1 e) none).map fun h => (h, h, (0 : Int))).orElse fun _ =>
      (wind c E as mSum fuel (Nat.sub skip 1) (Nat.mul 2 n0) (Nat.add n0 n1) (Nat.add e 1)).bind fun r1 =>
        (wind c E as mSum fuel (Nat.sub skip 1) (Nat.add n0 n1) (Nat.mul 2 n1) (Nat.add e 1)).map fun r2 =>
          (r1.1, r2.2.1, r1.2.2 + r2.2.2 + jmpI r1.2.1 r2.1)

def windOdd (g : Glob) (E : EllB) (as : List (Q × Q)) (mSum : Nat) : Bool :=
  (wind ⟨g.P, g.n, g.k⟩ E as mSum (Nat.add g.dW 1) 6 0 1 0).any fun r => (r.2.2 + jmpI r.2.1 r.1) % 2 == 1

/-! ## Witness leaves -/

def tileOf (g : Glob) (i : Nat) : Option EllB := (g.tiles[i]?).map (ellOf g.P)

def pinsIn (c : Cfg) (as : List (Q × Q)) : List (KCBall × PtT × Q) → List Box4 → Bool
  | p :: ps, B :: bs => ((sumK c p.1 as).any fun w => inBox w B) && pinsIn c as ps bs
  | _, _ => true

def witBall (g : Glob) (A : ACtx) (B : List Box4) (E : EllB) (w : WitD) (mn : Int) (md r' : Nat) (wz : KCBall) :
    Bool :=
  Nat.ble A.r r' && Nat.ble (normHi (KCBall.sub wz (KCBall.mulR g.P (qBall g.P w.sg) A.Sc))) r' &&
    pinsIn ⟨g.P, g.n, g.k⟩ w.as A.pins B && checkTAs g A E r' w.tw.n.toNat w.tw.d B w.N 0 w.dat &&
    windOdd g E w.as (KBall.cdiv (Nat.mul mn.toNat (Nat.pow 2 g.P)) md)

def witOK (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) : Bool :=
  (tileOf g w.ti).any fun E => (atomsOK w.as).any fun mm =>
    witExact g w mm.1 mm.2 &&
      ((rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX).any fun r' =>
        (sumK ⟨g.P, g.n, g.k⟩ A.zc w.as).any fun wz => witBall g A (pinBoxes g.P A.pins bx) E w mm.1 mm.2 r' wz)

def checkWit (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) : Bool := witOK g A bx (rdWit dat)

/-! ## Type H arcs -/

def walk (g : Glob) (A : ACtx) : Tree → List (Nat × Nat × Nat) → Bool
  | .excl dat, bx => checkExcl g A bx dat
  | .wit dat, bx => checkWit g A bx dat
  | .split j c0 c1 c2 c3, bx =>
    decide (j < bx.length) &&
      walk g A c0 (bx.set j (kid (bx.getD j (0, 0, 0)) 0)) && walk g A c1 (bx.set j (kid (bx.getD j (0, 0, 0)) 1)) &&
      walk g A c2 (bx.set j (kid (bx.getD j (0, 0, 0)) 2)) && walk g A c3 (bx.set j (kid (bx.getD j (0, 0, 0)) 3))

def pinROK (g : Glob) (p : KCBall) (R : Q) : Bool :=
  (expPiHi ⟨g.P, g.n, g.k⟩ (absHi p.im)).any fun eY => blt 0 R.d &&
    SI.le (SI.ofNat (mulU g.P (KBall.cdiv (Nat.mul g.tau.n.toNat (Nat.pow 2 g.P)) g.tau.d) eY)) (loS (qBall g.P R))

def T1B (g : Glob) : EllB := ellOf g.P (g.c, ⟨0, 1⟩, g.a, g.b)

def pinBall (P : Nat) (p : Q × Q) : KCBall := ⟨qBall P p.1, qBall P p.2⟩

def arcCtx (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) : Option ACtx :=
  (ellPt ⟨g.P, g.n, g.k⟩ (T1B g) (dyB g.P sc g.ES)).bind fun zc =>
  (cSS1 ⟨g.P, g.n, g.k⟩ zc).bind fun ss =>
  (ptT ⟨g.P, g.n, g.k⟩ g.D zc).bind fun zT =>
  (rBound g (T1B g) g.tau.n.toNat g.tau.d s0 s1 sc zc ss.1 ss.2 rX).bind fun r =>
  ((pins.map (pinBall g.P)).mapM (ptT ⟨g.P, g.n, g.k⟩ g.D)).map fun pts =>
    ⟨T1B g, s0, s1, sc, zc, ss.1, ss.2, zT, r, (pins.map (pinBall g.P)).zip (pts.zip Rs)⟩

def hHead (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) : Bool :=
  Nat.ble s0 sc && Nat.ble sc s1 && blt s0 s1 && Nat.beq pins.length Rs.length &&
    pins.all (fun p => blt 0 p.1.d && blt 0 p.2.d) &&
    ((pins.map (pinBall g.P)).zip Rs).all (fun x => pinROK g x.1 x.2)

def checkH (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : Tree) : Bool :=
  hHead g s0 s1 sc pins Rs && (arcCtx g s0 s1 sc pins Rs rX).any fun A => walk g A t (pins.map fun _ => (0, 0, 0))

def checkArc (g : Glob) : Arc → Bool
  | .E s0 s1 ur ui => blt s0 s1 && checkE g (T1B g) (intC g.P (ur, ui)) g.dE s0 s1 g.ES
  | .H s0 s1 sc pins Rs rX t => checkH g s0 s1 sc pins Rs rX t

/-! ## Global conditions -/

def checkGlob (g : Glob) : Bool := globParams g && windOdd g (T1B g) [] 0

end C64KChk
