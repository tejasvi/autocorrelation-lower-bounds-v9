import C64Core.Ival

/-!
# Complex balls and the functions of the c64 checker (core Lean only)

A complex ball is a pair of real balls (real and imaginary part) at a fixed precision `P`.  The functions:
* `ckt t z`: `K_t(z) = exp(-2πitz) = e^{2π t Im z} (cos(2π t Re z) - i sin(2π t Re z))`;
* `csinPi z`, `ccosPi z`: `sin(πz)`, `cos(πz)` through `cosh`, `sinh` of `π Im z` and `cos`, `sin` of `π Re z`;
* `cS z = sin(πz)/(πz)`, `cS1 z = (πz cos(πz) - sin(πz))/(πz²)`;
* `normHi`, `normLo`: upper and lower bounds of `|z|` (in units `2^-P`).
Every function returns `none` when an enclosure fails (e.g. a division by a ball that contains `0`).
-/

namespace C64Num

open Ival Ival.Ball

/-- Precision and Taylor parameters of the checker. -/
structure Cfg where
  P : Nat
  n : Nat
  k : Nat

/-- A complex ball: real and imaginary parts. -/
structure CBall where
  re : Ball
  im : Ball
deriving Repr, Inhabited

namespace CBall

def add (a b : CBall) : CBall := ⟨Ball.add a.re b.re, Ball.add a.im b.im⟩
def sub (a b : CBall) : CBall := ⟨Ball.sub a.re b.re, Ball.sub a.im b.im⟩
def neg (a : CBall) : CBall := ⟨Ball.neg a.re, Ball.neg a.im⟩
def conj (a : CBall) : CBall := ⟨a.re, Ball.neg a.im⟩

/-- `(a + bi)(c + di) = (ac - bd) + (ad + bc) i`. -/
def mul (P : Nat) (a b : CBall) : CBall :=
  ⟨Ball.sub (Ball.mul P a.re b.re) (Ball.mul P a.im b.im), Ball.add (Ball.mul P a.re b.im) (Ball.mul P a.im b.re)⟩

/-- Multiplication by a real ball. -/
def mulR (P : Nat) (x : Ball) (a : CBall) : CBall := ⟨Ball.mul P x a.re, Ball.mul P x a.im⟩

/-- The exact complex number `(a/b) + (c/d) i`, rounded. -/
def ofRat (P : Nat) (a : Int) (b : Nat) (c : Int) (d : Nat) : CBall := ⟨Ball.ofRat P a b, Ball.ofRat P c d⟩

end CBall

/-- Upper bound of `√n` for `n : Nat`. -/
def sqrtHi (n : Nat) : Nat := Nat.sqrt n + 1

/-- Upper bound (units `2^-P`) of `|z|`. -/
def normHi (a : CBall) : Nat := sqrtHi (a.re.absHi ^ 2 + a.im.absHi ^ 2)

/-- Lower end (units `2^-P`) of `|x|` on a real ball (`0` if the ball contains `0`). -/
def absLo (a : Ball) : Nat := a.m.natAbs - a.r

/-- Lower bound (units `2^-P`) of `|z|`. -/
def normLo (a : CBall) : Nat := Nat.sqrt (absLo a.re ^ 2 + absLo a.im ^ 2)

/-- Reciprocal of a ball contained in `(0, ∞)`: the interval `[2^{2P}/(m + r), 2^{2P}/(m - r)]` (units `2^-P`),
rounded outward; `none` if `m - r ≤ 0`. -/
def recipPos (P : Nat) (a : Ball) : Option Ball :=
  if (a.r : Int) < a.m then
    let num : Nat := 2 ^ (2 * P)
    let lo : Nat := num / (a.m.toNat + a.r)
    let hi : Nat := Ball.cdiv num (a.m.toNat - a.r)
    some ⟨((lo + hi) / 2 : Nat), (hi - (lo + hi) / 2 : Nat)⟩
  else none

/-- Division of complex balls: `w / z = w conj(z) / |z|²`; `none` if `|z|²` is not certainly positive. -/
def cdiv (P : Nat) (w z : CBall) : Option CBall :=
  let n2 := Ball.add (Ball.mul P z.re z.re) (Ball.mul P z.im z.im)
  (recipPos P n2).map fun q => CBall.mulR P q (CBall.mul P w (CBall.conj z))

/-- `K_t(z) = e^{2π t Im z} (cos(2π t Re z) - i sin(2π t Re z))`. -/
def ckt (c : Cfg) (t : Ball) (z : CBall) : Option CBall :=
  let pi := piB c.P
  let ex := Ball.mul c.P (Ball.mulInt 2 (Ball.mul c.P pi t)) z.im
  (expB c.P c.n ex).bind fun e =>
    (cosSinTurn c.P c.n c.k (Ball.mul c.P t z.re)).map fun cs =>
      ⟨Ball.mul c.P e cs.1, Ball.neg (Ball.mul c.P e cs.2)⟩

/-- `(cosh(π y), sinh(π y))` from `e^{±π y}`. -/
def coshSinhPi (c : Cfg) (y : Ball) : Option (Ball × Ball) :=
  let py := Ball.mul c.P (piB c.P) y
  (expB c.P c.n py).bind fun ep => (expB c.P c.n (Ball.neg py)).map fun em =>
    (Ball.shr 1 (Ball.add ep em), Ball.shr 1 (Ball.sub ep em))

/-- `(cos(πz), sin(πz))` for `z = x + iy`: `cos(πz) = cos(πx) cosh(πy) - i sin(πx) sinh(πy)`,
`sin(πz) = sin(πx) cosh(πy) + i cos(πx) sinh(πy)`. -/
def ccosSinPi (c : Cfg) (z : CBall) : Option (CBall × CBall) :=
  (cosSinTurn c.P c.n c.k (Ball.shr 1 z.re)).bind fun cs =>
    (coshSinhPi c z.im).map fun hs =>
      (⟨Ball.mul c.P cs.1 hs.1, Ball.neg (Ball.mul c.P cs.2 hs.2)⟩,
       ⟨Ball.mul c.P cs.2 hs.1, Ball.mul c.P cs.1 hs.2⟩)

/-- `S(z) = sin(πz)/(πz)`. -/
def cS (c : Cfg) (z : CBall) : Option CBall :=
  (ccosSinPi c z).bind fun cs => cdiv c.P cs.2 (CBall.mulR c.P (piB c.P) z)

/-- `S'(z) = (πz cos(πz) - sin(πz)) / (π z²)`. -/
def cS1 (c : Cfg) (z : CBall) : Option CBall :=
  (ccosSinPi c z).bind fun cs =>
    let pz := CBall.mulR c.P (piB c.P) z
    cdiv c.P (CBall.sub (CBall.mul c.P pz cs.1) cs.2) (CBall.mul c.P pz z)

/-- `(S(z), S'(z))` from one evaluation of `cos(πz)`, `sin(πz)`. -/
def cSS1 (c : Cfg) (z : CBall) : Option (CBall × CBall) :=
  (ccosSinPi c z).bind fun cs =>
    let pz := CBall.mulR c.P (piB c.P) z
    (cdiv c.P cs.2 pz).bind fun s =>
      (cdiv c.P (CBall.sub (CBall.mul c.P pz cs.1) cs.2) (CBall.mul c.P pz z)).map fun s1 => (s, s1)

end C64Num
