/-!
# Ball arithmetic over fixed-point dyadic numbers (core Lean only)

A ball `⟨m, r⟩` at precision `P` stands for the closed interval `[(m - r) / 2^P, (m + r) / 2^P]`
(`m : Int`, `r : Nat`).  Every operation rounds the centre to nearest and adds the rounding error (at most
one unit) to the radius.  Soundness is proved in `C64.Ival.Sound`.

Transcendental functions:
* `expB`: `exp x = (exp (x / 2^k))^(2^k)`, Taylor polynomial for `|x / 2^k| ≤ 1` with the remainder
  bound of `Real.exp_bound`;
* `cosSinTurn`: `(cos 2πu, sin 2πu)`; `u` is first reduced by an integer (exactly), then
  `θ = 2πu / 2^k` gets the Taylor polynomials of `cos`/`sin` (the real and imaginary parts of the
  exponential series at `iθ`, remainder of `Complex.exp_bound`), followed by `k` angle doublings.
-/

namespace Ival

/-- `⟨m, r⟩` stands for `[(m - r)/2^P, (m + r)/2^P]`. -/
structure Ball where
  m : Int
  r : Nat
deriving Repr, Inhabited

namespace Ball

/-- `p / 2^k` rounded to nearest (ties up); the error is at most `2^k / 2`. -/
@[inline] def rnd2 (p : Int) (k : Nat) : Int := (p + ((2 ^ k / 2 : Nat) : Int)) / ((2 ^ k : Nat) : Int)

/-- `p / d` rounded to nearest, for `d > 0`. -/
@[inline] def rndN (p : Int) (d : Nat) : Int := (p + ((d / 2 : Nat) : Int)) / (d : Int)

/-- Ceiling division on `Nat` (for `d > 0`). -/
@[inline] def cdiv (n d : Nat) : Nat := (n + d - 1) / d

/-- The exact integer `n`. -/
def ofInt (P : Nat) (n : Int) : Ball := ⟨n * ((2 ^ P : Nat) : Int), 0⟩

/-- The rational `num / den` (`den > 0`), rounded to nearest, radius one unit. -/
def ofRat (P : Nat) (num : Int) (den : Nat) : Ball := ⟨rndN (num * ((2 ^ P : Nat) : Int)) den, 1⟩

def add (a b : Ball) : Ball := ⟨a.m + b.m, a.r + b.r⟩
def neg (a : Ball) : Ball := ⟨-a.m, a.r⟩
def sub (a b : Ball) : Ball := ⟨a.m - b.m, a.r + b.r⟩

/-- Product: `|xy - ab| ≤ |a| s + |b| r + r s` for `|x - a| ≤ r`, `|y - b| ≤ s`, then rounding. -/
def mul (P : Nat) (a b : Ball) : Ball :=
  ⟨rnd2 (a.m * b.m) P, cdiv (a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r) (2 ^ P) + 1⟩

/-- Multiplication by an integer (exact). -/
def mulInt (n : Int) (a : Ball) : Ball := ⟨n * a.m, n.natAbs * a.r⟩

/-- Division by `2^k`. -/
def shr (k : Nat) (a : Ball) : Ball := ⟨rnd2 a.m k, cdiv a.r (2 ^ k) + 1⟩

/-- Division by a positive natural number `d`. -/
def divNat (d : Nat) (a : Ball) : Ball := ⟨rndN a.m d, cdiv a.r d + 1⟩

/-- Upper bound (in units `2^-P`) of `|x|` on the ball. -/
@[inline] def absHi (a : Ball) : Nat := a.m.natAbs + a.r

/-- The ball lies in `(0, ∞)`. -/
@[inline] def isPos (a : Ball) : Bool := decide ((a.r : Int) < a.m)

/-- The ball lies in `(-∞, 0)`. -/
@[inline] def isNeg (a : Ball) : Bool := decide (a.m + (a.r : Int) < 0)

/-- Lower end `(m - r)` and upper end `(m + r)` in units `2^-P`. -/
@[inline] def lo (a : Ball) : Int := a.m - a.r
@[inline] def hi (a : Ball) : Int := a.m + a.r

/-- Taylor terms `x^j / j!` for `j < n` and their sums: returns `(Σ_{j<n} x^j/j!, x^n/n!)`
by the recursion `T_{j+1} = T_j x / (j+1)`; the sums are split into even and odd `j`, with the signs
`(-1)^(j/2)` (for the series of `cos`/`sin`) when `alt = true`. -/
def taylorAux (P : Nat) (alt : Bool) (x : Ball) : Nat → Nat → Ball → Ball → Ball → Ball × Ball
  | 0, _, _, ev, od => (ev, od)
  | fuel + 1, j, t, ev, od =>
    let ev' := if j % 2 == 0 then (if alt && j % 4 == 2 then sub ev t else add ev t) else ev
    let od' := if j % 2 == 1 then (if alt && j % 4 == 3 then sub od t else add od t) else od
    taylorAux P alt x fuel (j + 1) (divNat (j + 1) (mul P t x)) ev' od'

/-- `n!` (core Lean has no factorial). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The remainder bound `M^n (n+1) / (n! n)` of `Real.exp_bound`, in units `2^-P`, rounded up,
for `M = mh / 2^P`. -/
def remBound (P n mh : Nat) : Nat :=
  cdiv (mh ^ n * (n + 1)) (fact n * n * 2 ^ (P * (n - 1)))

/-- Taylor enclosure of `exp x` for `|x| ≤ 1` (`n ≥ 1` terms); `none` if `|x| ≤ 1` is not certain. -/
def expSmall (P n : Nat) (x : Ball) : Option Ball :=
  if x.absHi ≤ 2 ^ P ∧ 0 < n then
    let (ev, od) := taylorAux P false x n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
    let s := add ev od
    some ⟨s.m, s.r + remBound P n x.absHi⟩
  else none

/-- Repeated squaring. -/
def sqIter (P : Nat) : Nat → Ball → Ball
  | 0, a => a
  | k + 1, a => sqIter P k (mul P a a)

/-- Smallest `k ≤ fuel` with `h ≤ 2^(P + k - 1)` (so that `h / 2^k ≤ 2^P / 2`). -/
def findShift (P h : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => if 2 * h ≤ 2 ^ (P + k) then k else findShift P h fuel (k + 1)

/-- `exp` on a ball. -/
def expB (P n : Nat) (x : Ball) : Option Ball :=
  let k := findShift P x.absHi 64 0
  match expSmall P n (shr k x) with
  | some e => some (sqIter P k e)
  | none => none

/-- `exp` with a fast path: for `x ≤ -P` the ball `⟨0, 1⟩` (as `e^{-P} ≤ 2^{-P}`). -/
def expB' (P n : Nat) (x : Ball) : Option Ball :=
  if x.hi ≤ -((P : Int) * ((2 ^ P : Nat) : Int)) then some ⟨0, 1⟩ else expB P n x

/-- `|x|`. -/
def absB (a : Ball) : Ball := ⟨a.m.natAbs, a.r⟩

/-- A ball containing the balls `a` and `b`. -/
def hullB (a b : Ball) : Ball :=
  let lo := min a.lo b.lo
  let hi := max a.hi b.hi
  let m := (lo + hi) / 2
  ⟨m, (max (hi - m) (m - lo)).toNat⟩

/-- `exp` on a ball by monotonicity: the hull of the enclosures at the two end points. -/
def expH (P n : Nat) (x : Ball) : Option Ball :=
  (expB' P n ⟨x.m - x.r, 0⟩).bind fun e1 => (expB' P n ⟨x.m + x.r, 0⟩).bind fun e2 => some (hullB e1 e2)

/-- The ball `[π]` from Mathlib's 20-digit bounds `3.14159265358979323846 < π < 3.14159265358979323847`. -/
def piB (P : Nat) : Ball :=
  -- centre: the midpoint 314159265358979323846.5 / 10^20, radius 0.5e-20 plus rounding
  ⟨rndN (628318530717958647693 * ((2 ^ P : Nat) : Int)) (2 * 10 ^ 20),
    cdiv (2 ^ P) (2 * 10 ^ 20) + 1⟩

/-- Enclosures of `(cos θ, sin θ)` for `|θ| ≤ 1` (`n ≥ 1` terms). -/
def cosSinSmall (P n : Nat) (θ : Ball) : Option (Ball × Ball) :=
  if θ.absHi ≤ 2 ^ P ∧ 0 < n then
    let (ev, od) := taylorAux P true θ n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
    let e := remBound P n θ.absHi
    some (⟨ev.m, ev.r + e⟩, ⟨od.m, od.r + e⟩)
  else none

/-- `k` angle doublings: `(c, s) ↦ (c² - s², 2cs)`. -/
def dblIter (P : Nat) : Nat → Ball × Ball → Ball × Ball
  | 0, cs => cs
  | k + 1, (c, s) => dblIter P k (sub (mul P c c) (mul P s s), mulInt 2 (mul P c s))

/-- `u` minus its nearest integer (exact). -/
def fracTurn (P : Nat) (u : Ball) : Ball := ⟨u.m - rnd2 u.m P * ((2 ^ P : Nat) : Int), u.r⟩

/-- The angle `2π (u - round u) / 2^k`. -/
def turnArg (P k : Nat) (u : Ball) : Ball := shr k (mul P (mulInt 2 (piB P)) (fracTurn P u))

/-- `(cos 2πu, sin 2πu)`: reduce `u` by the nearest integer, then `θ = 2πu / 2^k` with `k` doublings. -/
def cosSinTurn (P n k : Nat) (u : Ball) : Option (Ball × Ball) :=
  (cosSinSmall P n (turnArg P k u)).map (dblIter P k)

/-- `(cos 2πu, sin 2πu)` on a ball by the centred form: the enclosures at the centre, widened by
`2π · rad` (`2π < 6.2832`). -/
def cosSinTurnC (P n k : Nat) (u : Ball) : Option (Ball × Ball) :=
  (cosSinTurn P n k ⟨u.m, 0⟩).map fun cs =>
    (⟨cs.1.m, cs.1.r + cdiv (u.r * 62832) 10000⟩, ⟨cs.2.m, cs.2.r + cdiv (u.r * 62832) 10000⟩)

end Ball
end Ival
