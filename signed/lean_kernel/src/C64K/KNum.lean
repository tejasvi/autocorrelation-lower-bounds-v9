import C64K.KBall

/-!
# Complex sign-magnitude balls and the functions of the c64 checker (kernel layer)

Mirrors `C64Core.Num` (`C64Num`) on `KIval.KBall`: every function computes exactly what the `C64Num` function computes
on the corresponding `Ival.Ball` values (simulation lemmas in `C64K.KNumSim`).
-/

namespace KNum

open KIval KIval.KBall

/-- Precision and Taylor parameters (as `C64Num.Cfg`). -/
structure Cfg where
  P : Nat
  n : Nat
  k : Nat

/-- A complex ball: real and imaginary parts. -/
structure KCBall where
  re : KBall
  im : KBall
deriving Repr, Inhabited

namespace KCBall

def add (a b : KCBall) : KCBall := ⟨KBall.add a.re b.re, KBall.add a.im b.im⟩
def sub (a b : KCBall) : KCBall := ⟨KBall.sub a.re b.re, KBall.sub a.im b.im⟩
def neg (a : KCBall) : KCBall := ⟨KBall.neg a.re, KBall.neg a.im⟩
def conj (a : KCBall) : KCBall := ⟨a.re, KBall.neg a.im⟩

/-- `(a + bi)(c + di) = (ac - bd) + (ad + bc) i`. -/
def mul (P : Nat) (a b : KCBall) : KCBall :=
  ⟨KBall.sub (KBall.mul P a.re b.re) (KBall.mul P a.im b.im),
   KBall.add (KBall.mul P a.re b.im) (KBall.mul P a.im b.re)⟩

/-- Multiplication by a real ball. -/
def mulR (P : Nat) (x : KBall) (a : KCBall) : KCBall := ⟨KBall.mul P x a.re, KBall.mul P x a.im⟩

/-- The exact complex number `(-1)^sa a/b + (-1)^sc (c/d) i`, rounded. -/
def ofRat (P : Nat) (sa : Bool) (a b : Nat) (sc : Bool) (c d : Nat) : KCBall :=
  ⟨KBall.ofRat P sa a b, KBall.ofRat P sc c d⟩

end KCBall

/-- Upper bound of `√n`. -/
def sqrtHi (n : Nat) : Nat := Nat.add (Nat.sqrt n) 1

/-- Upper bound (units `2^-P`) of `|z|`. -/
def normHi (a : KCBall) : Nat := sqrtHi (Nat.add (Nat.pow (absHi a.re) 2) (Nat.pow (absHi a.im) 2))

/-- Lower end (units `2^-P`) of `|x|` on a real ball. -/
def absLo (a : KBall) : Nat := Nat.sub a.m a.r

/-- Lower bound (units `2^-P`) of `|z|`. -/
def normLo (a : KCBall) : Nat := Nat.sqrt (Nat.add (Nat.pow (absLo a.re) 2) (Nat.pow (absLo a.im) 2))

/-- Reciprocal of a ball contained in `(0, ∞)`, as `C64Num.recipPos`. -/
def recipPos (P : Nat) (a : KBall) : Option KBall :=
  cond (isPos a)
    (let num := Nat.pow 2 (Nat.mul 2 P)
     let lo := Nat.div num (Nat.add a.m a.r)
     let hi := KBall.cdiv num (Nat.sub a.m a.r)
     let c := Nat.div (Nat.add lo hi) 2
     some ⟨false, c, Nat.sub hi c⟩)
    none

/-- Division of complex balls, as `C64Num.cdiv`. -/
def cdiv (P : Nat) (w z : KCBall) : Option KCBall :=
  let n2 := KBall.add (KBall.mul P z.re z.re) (KBall.mul P z.im z.im)
  (recipPos P n2).map fun q => KCBall.mulR P q (KCBall.mul P w (KCBall.conj z))

/-- `K_t(z) = e^{2π t Im z} (cos(2π t Re z) - i sin(2π t Re z))`, as `C64Num.ckt`. -/
def ckt (c : Cfg) (t : KBall) (z : KCBall) : Option KCBall :=
  let pi := piB c.P
  let ex := KBall.mul c.P (KBall.mulInt false 2 (KBall.mul c.P pi t)) z.im
  (expB c.P c.n ex).bind fun e =>
    (cosSinTurn c.P c.n c.k (KBall.mul c.P t z.re)).map fun cs =>
      ⟨KBall.mul c.P e cs.1, KBall.neg (KBall.mul c.P e cs.2)⟩

/-- `(cosh(π y), sinh(π y))`, as `C64Num.coshSinhPi`. -/
def coshSinhPi (c : Cfg) (y : KBall) : Option (KBall × KBall) :=
  let py := KBall.mul c.P (piB c.P) y
  (expB c.P c.n py).bind fun ep => (expB c.P c.n (KBall.neg py)).map fun em =>
    (KBall.shr 1 (KBall.add ep em), KBall.shr 1 (KBall.sub ep em))

/-- `(cos(πz), sin(πz))`, as `C64Num.ccosSinPi`. -/
def ccosSinPi (c : Cfg) (z : KCBall) : Option (KCBall × KCBall) :=
  (cosSinTurn c.P c.n c.k (KBall.shr 1 z.re)).bind fun cs =>
    (coshSinhPi c z.im).map fun hs =>
      (⟨KBall.mul c.P cs.1 hs.1, KBall.neg (KBall.mul c.P cs.2 hs.2)⟩,
       ⟨KBall.mul c.P cs.2 hs.1, KBall.mul c.P cs.1 hs.2⟩)

/-- `S(z) = sin(πz)/(πz)`. -/
def cS (c : Cfg) (z : KCBall) : Option KCBall :=
  (ccosSinPi c z).bind fun cs => cdiv c.P cs.2 (KCBall.mulR c.P (piB c.P) z)

/-- `S'(z) = (πz cos(πz) - sin(πz)) / (π z²)`. -/
def cS1 (c : Cfg) (z : KCBall) : Option KCBall :=
  (ccosSinPi c z).bind fun cs =>
    let pz := KCBall.mulR c.P (piB c.P) z
    cdiv c.P (KCBall.sub (KCBall.mul c.P pz cs.1) cs.2) (KCBall.mul c.P pz z)

/-- `(S(z), S'(z))` from one evaluation of `cos(πz)`, `sin(πz)`. -/
def cSS1 (c : Cfg) (z : KCBall) : Option (KCBall × KCBall) :=
  (ccosSinPi c z).bind fun cs =>
    let pz := KCBall.mulR c.P (piB c.P) z
    (cdiv c.P cs.2 pz).bind fun s =>
      (cdiv c.P (KCBall.sub (KCBall.mul c.P pz cs.1) cs.2) (KCBall.mul c.P pz z)).map fun s1 => (s, s1)

end KNum
