/-!
# Sign-magnitude ball arithmetic for the kernel (core Lean only)

`KIval.KBall` mirrors `Ival.Ball` with the centre stored as a sign and a magnitude: `⟨s, m, r⟩` stands for the ball
`⟨(-1)^s m, r⟩` of `Ival.Ball` (`KBall.toBall`).  Every operation computes exactly what the `Ival` operation computes
(same rounding), so that `toBall (opK ..) = op (toBall ..)` (the simulation lemmas of `C64K.KBallSim`).

Kernel-oriented style: the natural-number primitives that the kernel evaluates on literals (`Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.ble`, `Nat.beq`) are called directly (no `HAdd`/`HMul`/`Decidable`
instance unfolding), branching is `cond` on `Bool`, and no definition matches on a computed value (projections
only).
-/

namespace KIval

/-- `⟨s, m, r⟩` stands for `[((-1)^s m - r)/2^P, ((-1)^s m + r)/2^P]`. -/
structure KBall where
  s : Bool
  m : Nat
  r : Nat
deriving Repr, Inhabited

namespace KBall

/-- Exclusive or. -/
@[inline] def bx (a b : Bool) : Bool := cond a (cond b false true) b

/-- `a < b` on `Nat`. -/
@[inline] def blt (a b : Nat) : Bool := Nat.ble (Nat.add a 1) b

/-- `(-1)^s m / d` rounded to nearest (ties up, i.e. `((-1)^s m + ⌊d/2⌋) ediv d` as in `Ival.Ball.rndN`), with
radius `r`. -/
@[inline] def rndD (s : Bool) (m d r : Nat) : KBall :=
  let h := Nat.div d 2
  cond s
    (cond (Nat.ble m h) ⟨false, 0, r⟩ ⟨true, Nat.div (Nat.sub (Nat.add m d) (Nat.add h 1)) d, r⟩)
    ⟨false, Nat.div (Nat.add m h) d, r⟩

/-- Ceiling division on `Nat` (for `d > 0`), as `Ival.Ball.cdiv`. -/
@[inline] def cdiv (n d : Nat) : Nat := Nat.div (Nat.sub (Nat.add n d) 1) d

/-- The exact integer `(-1)^s n`. -/
def ofInt (P : Nat) (s : Bool) (n : Nat) : KBall := ⟨s, Nat.mul n (Nat.pow 2 P), 0⟩

/-- The rational `(-1)^s num / den` (`den > 0`), rounded to nearest, radius one unit. -/
def ofRat (P : Nat) (s : Bool) (num den : Nat) : KBall := rndD s (Nat.mul num (Nat.pow 2 P)) den 1

/-- Signed sum `(-1)^s₁ a + (-1)^s₂ b` with radius `r`. -/
@[inline] def sadd (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) : KBall :=
  cond (bx s₁ s₂)
    (cond (Nat.ble b a) ⟨s₁, Nat.sub a b, r⟩ ⟨s₂, Nat.sub b a, r⟩)
    ⟨s₁, Nat.add a b, r⟩

def add (a b : KBall) : KBall := sadd a.s a.m b.s b.m (Nat.add a.r b.r)
def neg (a : KBall) : KBall := ⟨cond a.s false true, a.m, a.r⟩
def sub (a b : KBall) : KBall := sadd a.s a.m (cond b.s false true) b.m (Nat.add a.r b.r)

/-- Product, as `Ival.Ball.mul`. -/
def mul (P : Nat) (a b : KBall) : KBall :=
  let d := Nat.pow 2 P
  rndD (bx a.s b.s) (Nat.mul a.m b.m) d
    (Nat.add (cdiv (Nat.add (Nat.add (Nat.mul a.m b.r) (Nat.mul b.m a.r)) (Nat.mul a.r b.r)) d) 1)

/-- Multiplication by the integer `(-1)^s n` (exact). -/
def mulInt (s : Bool) (n : Nat) (a : KBall) : KBall := ⟨bx s a.s, Nat.mul n a.m, Nat.mul n a.r⟩

/-- Division by `2^k`. -/
def shr (k : Nat) (a : KBall) : KBall :=
  let d := Nat.pow 2 k
  rndD a.s a.m d (Nat.add (cdiv a.r d) 1)

/-- Division by a positive natural number `d`. -/
def divNat (d : Nat) (a : KBall) : KBall := rndD a.s a.m d (Nat.add (cdiv a.r d) 1)

/-- Upper bound (in units `2^-P`) of `|x|` on the ball. -/
@[inline] def absHi (a : KBall) : Nat := Nat.add a.m a.r

/-- The ball lies in `(0, ∞)`. -/
@[inline] def isPos (a : KBall) : Bool := cond a.s false (blt a.r a.m)

/-- The ball lies in `(-∞, 0)`. -/
@[inline] def isNeg (a : KBall) : Bool := cond a.s (blt a.r a.m) false

/-- Taylor terms, as `Ival.Ball.taylorAux`. -/
def taylorAux (P : Nat) (alt : Bool) (x : KBall) : Nat → Nat → KBall → KBall → KBall → KBall × KBall
  | 0, _, _, ev, od => (ev, od)
  | fuel + 1, j, t, ev, od =>
    let j2 := Nat.mod j 2
    let j4 := Nat.mod j 4
    let ev' := cond (Nat.beq j2 0) (cond (cond alt (Nat.beq j4 2) false) (sub ev t) (add ev t)) ev
    let od' := cond (Nat.beq j2 1) (cond (cond alt (Nat.beq j4 3) false) (sub od t) (add od t)) od
    taylorAux P alt x fuel (Nat.add j 1) (divNat (Nat.add j 1) (mul P t x)) ev' od'

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.mul (Nat.add n 1) (fact n)

/-- The remainder bound of `Ival.Ball.remBound`. -/
def remBound (P n mh : Nat) : Nat :=
  cdiv (Nat.mul (Nat.pow mh n) (Nat.add n 1)) (Nat.mul (Nat.mul (fact n) n) (Nat.pow 2 (Nat.mul P (Nat.sub n 1))))

/-- Taylor enclosure of `exp x` for `|x| ≤ 1`, as `Ival.Ball.expSmall`. -/
def expSmall (P n : Nat) (x : KBall) : Option KBall :=
  cond (cond (Nat.ble (absHi x) (Nat.pow 2 P)) (blt 0 n) false)
    (let eo := taylorAux P false x n 0 (ofInt P false 1) ⟨false, 0, 0⟩ ⟨false, 0, 0⟩
     let s := add eo.1 eo.2
     some ⟨s.s, s.m, Nat.add s.r (remBound P n (absHi x))⟩)
    none

/-- Repeated squaring. -/
def sqIter (P : Nat) : Nat → KBall → KBall
  | 0, a => a
  | k + 1, a => sqIter P k (mul P a a)

/-- Smallest `k ≤ fuel` with `h ≤ 2^(P + k - 1)`, as `Ival.Ball.findShift`. -/
def findShift (P h : Nat) : Nat → Nat → Nat
  | 0, k => k
  | fuel + 1, k => cond (Nat.ble (Nat.mul 2 h) (Nat.pow 2 (Nat.add P k))) k (findShift P h fuel (Nat.add k 1))

/-- `exp` on a ball. -/
def expB (P n : Nat) (x : KBall) : Option KBall :=
  let k := findShift P (absHi x) 64 0
  (expSmall P n (shr k x)).map (sqIter P k)

/-- `exp` with the fast path of `Ival.Ball.expB'` (`x ≤ -P` gives `⟨0, 1⟩`). -/
def expB' (P n : Nat) (x : KBall) : Option KBall :=
  let L := Nat.mul P (Nat.pow 2 P)
  cond (cond x.s (Nat.ble (Nat.add x.r L) x.m) (Nat.beq (Nat.add (Nat.add x.m x.r) L) 0))
    (some ⟨false, 0, 1⟩) (expB P n x)

/-- `|x|`. -/
def absB (a : KBall) : KBall := ⟨false, a.m, a.r⟩

/-! Signed integers `(-1)^s n` as pairs, for `hullB`. -/

/-- `(-1)^s₁ a ≤ (-1)^s₂ b`. -/
@[inline] def sle (s₁ : Bool) (a : Nat) (s₂ : Bool) (b : Nat) : Bool :=
  cond s₁ (cond s₂ (Nat.ble b a) true) (cond s₂ (cond (Nat.beq a 0) (Nat.beq b 0) false) (Nat.ble a b))

/-- A ball containing the balls `a` and `b`, as `Ival.Ball.hullB`. -/
def hullB (a b : KBall) : KBall :=
  -- lower ends `(-1)^s m - r` and upper ends `(-1)^s m + r` as signed pairs
  let la := sadd a.s a.m true a.r 0
  let lb := sadd b.s b.m true b.r 0
  let ha := sadd a.s a.m false a.r 0
  let hb := sadd b.s b.m false b.r 0
  let lo := cond (sle la.s la.m lb.s lb.m) la lb
  let hi := cond (sle ha.s ha.m hb.s hb.m) hb ha
  -- `m = (lo + hi) ediv 2` (floor)
  let sum := sadd lo.s lo.m hi.s hi.m 0
  let c' : KBall := cond sum.s ⟨true, Nat.div (Nat.add sum.m 1) 2, 0⟩ ⟨false, Nat.div sum.m 2, 0⟩
  -- radius `max (hi - m) (m - lo)` (clamped at `0`)
  let d1 := sadd hi.s hi.m (cond c'.s false true) c'.m 0
  let d2 := sadd c'.s c'.m (cond lo.s false true) lo.m 0
  let r1 := cond d1.s 0 d1.m
  let r2 := cond d2.s 0 d2.m
  ⟨c'.s, c'.m, cond (Nat.ble r1 r2) r2 r1⟩

/-- `exp` on a ball by monotonicity, as `Ival.Ball.expH`. -/
def expH (P n : Nat) (x : KBall) : Option KBall :=
  (expB' P n (sadd x.s x.m true x.r 0)).bind fun e1 =>
    (expB' P n (sadd x.s x.m false x.r 0)).bind fun e2 => some (hullB e1 e2)

/-- The ball `[π]`, as `Ival.Ball.piB`. -/
def piB (P : Nat) : KBall :=
  rndD false (Nat.mul 628318530717958647693 (Nat.pow 2 P)) (Nat.mul 2 (Nat.pow 10 20))
    (Nat.add (cdiv (Nat.pow 2 P) (Nat.mul 2 (Nat.pow 10 20))) 1)

/-- Enclosures of `(cos θ, sin θ)` for `|θ| ≤ 1`, as `Ival.Ball.cosSinSmall`. -/
def cosSinSmall (P n : Nat) (θ : KBall) : Option (KBall × KBall) :=
  cond (cond (Nat.ble (absHi θ) (Nat.pow 2 P)) (blt 0 n) false)
    (let eo := taylorAux P true θ n 0 (ofInt P false 1) ⟨false, 0, 0⟩ ⟨false, 0, 0⟩
     let e := remBound P n (absHi θ)
     some (⟨eo.1.s, eo.1.m, Nat.add eo.1.r e⟩, ⟨eo.2.s, eo.2.m, Nat.add eo.2.r e⟩))
    none

/-- `k` angle doublings `(c, s) ↦ (c² - s², 2cs)`. -/
def dblIter (P : Nat) : Nat → KBall × KBall → KBall × KBall
  | 0, cs => cs
  | k + 1, cs => dblIter P k (sub (mul P cs.1 cs.1) (mul P cs.2 cs.2), mulInt false 2 (mul P cs.1 cs.2))

/-- `u` minus its nearest integer (exact), as `Ival.Ball.fracTurn`. -/
def fracTurn (P : Nat) (u : KBall) : KBall :=
  let d := Nat.pow 2 P
  let q := rndD u.s u.m d 0
  sadd u.s u.m (cond q.s false true) (Nat.mul q.m d) u.r

/-- The angle `2π (u - round u) / 2^k`. -/
def turnArg (P k : Nat) (u : KBall) : KBall := shr k (mul P (mulInt false 2 (piB P)) (fracTurn P u))

/-- `(cos 2πu, sin 2πu)`, as `Ival.Ball.cosSinTurn`. -/
def cosSinTurn (P n k : Nat) (u : KBall) : Option (KBall × KBall) :=
  (cosSinSmall P n (turnArg P k u)).map (dblIter P k)

/-- The centred form `Ival.Ball.cosSinTurnC`. -/
def cosSinTurnC (P n k : Nat) (u : KBall) : Option (KBall × KBall) :=
  (cosSinTurn P n k ⟨u.s, u.m, 0⟩).map fun cs =>
    let w := cdiv (Nat.mul u.r 62832) 10000
    (⟨cs.1.s, cs.1.m, Nat.add cs.1.r w⟩, ⟨cs.2.s, cs.2.m, Nat.add cs.2.r w⟩)

end KBall
end KIval
