import C64K.KBallSim
import C64K.KNum
import C64Core.Num

/-!
# Simulation lemmas for the complex layer: `KNum` computes exactly what `C64Num` computes

`KCBall.toC ⟨re, im⟩ = ⟨toBall re, toBall im⟩`; for every function `f` of `C64Num` the lemma `toC_f` states
`toC (KNum.f ..) = C64Num.f (toC ..)` (with `Option.map` and `Prod.map` as needed).
-/

namespace KNum

open KIval KIval.KBall

/-- The configuration of `C64Num` with the same parameters. -/
def Cfg.toC (c : Cfg) : C64Num.Cfg := ⟨c.P, c.n, c.k⟩

namespace KCBall

/-- The `C64Num.CBall` that a `KCBall` stands for. -/
def toC (a : KCBall) : C64Num.CBall := ⟨toBall a.re, toBall a.im⟩

@[simp] lemma toC_re (a : KCBall) : (toC a).re = toBall a.re := rfl
@[simp] lemma toC_im (a : KCBall) : (toC a).im = toBall a.im := rfl

theorem toC_add (a b : KCBall) : toC (add a b) = C64Num.CBall.add (toC a) (toC b) := by
  simp [toC, add, C64Num.CBall.add, toBall_add]

theorem toC_sub (a b : KCBall) : toC (sub a b) = C64Num.CBall.sub (toC a) (toC b) := by
  simp [toC, sub, C64Num.CBall.sub, toBall_sub]

theorem toC_neg (a : KCBall) : toC (neg a) = C64Num.CBall.neg (toC a) := by
  simp [toC, neg, C64Num.CBall.neg, toBall_neg]

theorem toC_conj (a : KCBall) : toC (conj a) = C64Num.CBall.conj (toC a) := by
  simp [toC, conj, C64Num.CBall.conj, toBall_neg]

theorem toC_mul (P : Nat) (a b : KCBall) : toC (mul P a b) = C64Num.CBall.mul P (toC a) (toC b) := by
  simp [toC, mul, C64Num.CBall.mul, toBall_mul, toBall_sub, toBall_add]

theorem toC_mulR (P : Nat) (x : KBall) (a : KCBall) : toC (mulR P x a) = C64Num.CBall.mulR P (toBall x) (toC a) := by
  simp [toC, mulR, C64Num.CBall.mulR, toBall_mul]

theorem toC_ofRat (P : Nat) (sa : Bool) (a b : Nat) (sc : Bool) (c d : Nat) :
    toC (ofRat P sa a b sc c d) = C64Num.CBall.ofRat P (sval sa a) b (sval sc c) d := by
  simp [toC, ofRat, C64Num.CBall.ofRat, toBall_ofRat]

end KCBall

open KCBall

theorem normHi_eq (a : KCBall) : normHi a = C64Num.normHi (toC a) := by
  simp [normHi, C64Num.normHi, sqrtHi, C64Num.sqrtHi, absHi_eq]

theorem absLo_eq (a : KBall) : absLo a = C64Num.absLo (toBall a) := by
  simp [absLo, C64Num.absLo]

theorem normLo_eq (a : KCBall) : normLo a = C64Num.normLo (toC a) := by
  simp [normLo, C64Num.normLo, absLo_eq]

theorem toBall_recipPos (P : Nat) (a : KBall) : (recipPos P a).map toBall = C64Num.recipPos P (toBall a) := by
  dsimp only [recipPos, C64Num.recipPos]
  rw [isPos_eq]
  by_cases h : ((toBall a).r : Int) < (toBall a).m
  · have hp : Ival.Ball.isPos (toBall a) = true := decide_eq_true h
    have hs : a.s = false := by
      cases hs : a.s
      · rfl
      · simp [hs] at h; omega
    have hm : (toBall a).m.toNat = a.m := by simp [hs]
    simp only [hp, Bool.cond_true, h, ite_true, Option.map_some, hm]
    congr 1
  · have hp : Ival.Ball.isPos (toBall a) = false := decide_eq_false h
    simp only [hp, Bool.cond_false, h, ite_false, Option.map_none]

theorem toC_cdiv (P : Nat) (w z : KCBall) : (cdiv P w z).map toC = C64Num.cdiv P (toC w) (toC z) := by
  dsimp only [cdiv, C64Num.cdiv]
  have h := toBall_recipPos P (KBall.add (KBall.mul P z.re z.re) (KBall.mul P z.im z.im))
  rw [toBall_add, toBall_mul, toBall_mul] at h
  simp only [toC_re, toC_im]
  rw [← h]
  cases recipPos P (KBall.add (KBall.mul P z.re z.re) (KBall.mul P z.im z.im)) <;>
    simp [toC_mulR, toC_mul, toC_conj]

theorem toC_ckt (c : Cfg) (t : KBall) (z : KCBall) : (ckt c t z).map toC = C64Num.ckt c.toC (toBall t) (toC z) := by
  dsimp only [ckt, C64Num.ckt]
  have he := toBall_expB c.P c.n (KBall.mul c.P (KBall.mulInt false 2 (KBall.mul c.P (piB c.P) t)) z.im)
  simp only [toBall_mul, toBall_mulInt, toBall_piB] at he
  have hc := toBall_cosSinTurn c.P c.n c.k (KBall.mul c.P t z.re)
  rw [toBall_mul] at hc
  simp only [Cfg.toC, toC_im, toC_re]
  rw [← hc, show ((2 : Int)) = sval false 2 from rfl, ← he]
  cases expB c.P c.n (KBall.mul c.P (KBall.mulInt false 2 (KBall.mul c.P (piB c.P) t)) z.im) <;>
    cases cosSinTurn c.P c.n c.k (KBall.mul c.P t z.re) <;> simp [toC, toBall_mul, toBall_neg]

theorem toBall_coshSinhPi (c : Cfg) (y : KBall) :
    (coshSinhPi c y).map (Prod.map toBall toBall) = C64Num.coshSinhPi c.toC (toBall y) := by
  dsimp only [coshSinhPi, C64Num.coshSinhPi]
  have h1 := toBall_expB c.P c.n (KBall.mul c.P (piB c.P) y)
  have h2 := toBall_expB c.P c.n (KBall.neg (KBall.mul c.P (piB c.P) y))
  simp only [toBall_mul, toBall_piB, toBall_neg] at h1 h2
  simp only [Cfg.toC]
  rw [← h1, ← h2]
  cases expB c.P c.n (KBall.mul c.P (piB c.P) y) <;> cases expB c.P c.n (KBall.neg (KBall.mul c.P (piB c.P) y)) <;>
    simp [toBall_shr, toBall_add, toBall_sub]

theorem toC_ccosSinPi (c : Cfg) (z : KCBall) :
    (ccosSinPi c z).map (Prod.map toC toC) = C64Num.ccosSinPi c.toC (toC z) := by
  dsimp only [ccosSinPi, C64Num.ccosSinPi]
  have h1 := toBall_cosSinTurn c.P c.n c.k (KBall.shr 1 z.re)
  have h2 := toBall_coshSinhPi c z.im
  rw [toBall_shr] at h1
  simp only [Cfg.toC, toC_re, toC_im] at h2 ⊢
  rw [← h1, ← h2]
  cases cosSinTurn c.P c.n c.k (KBall.shr 1 z.re) <;> cases coshSinhPi c z.im <;>
    simp [toC, toBall_mul, toBall_neg]

theorem toC_cS (c : Cfg) (z : KCBall) : (cS c z).map toC = C64Num.cS c.toC (toC z) := by
  dsimp only [cS, C64Num.cS]
  rw [← toC_ccosSinPi]
  cases ccosSinPi c z with
  | none => rfl
  | some cs =>
    simp only [Option.map_some, Option.bind_some, Prod.map]
    rw [toC_cdiv, toC_mulR, toBall_piB]
    rfl

theorem toC_cS1 (c : Cfg) (z : KCBall) : (cS1 c z).map toC = C64Num.cS1 c.toC (toC z) := by
  dsimp only [cS1, C64Num.cS1]
  rw [← toC_ccosSinPi]
  cases ccosSinPi c z with
  | none => rfl
  | some cs =>
    simp only [Option.map_some, Option.bind_some, Prod.map]
    rw [toC_cdiv, toC_sub, toC_mul, toC_mul, toC_mulR, toBall_piB]
    rfl

theorem toC_cSS1 (c : Cfg) (z : KCBall) :
    (cSS1 c z).map (Prod.map toC toC) = C64Num.cSS1 c.toC (toC z) := by
  dsimp only [cSS1, C64Num.cSS1]
  rw [← toC_ccosSinPi]
  cases ccosSinPi c z with
  | none => rfl
  | some cs =>
    simp only [Option.map_some, Option.bind_some, Prod.map]
    have h1 := toC_cdiv c.P cs.2 (KCBall.mulR c.P (piB c.P) z)
    have h2 := toC_cdiv c.P (KCBall.sub (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) cs.1) cs.2)
      (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) z)
    simp only [toC_mulR, toC_sub, toC_mul, toBall_piB] at h1 h2
    simp only [Cfg.toC]
    rw [← h1, ← h2]
    cases cdiv c.P cs.2 (KCBall.mulR c.P (piB c.P) z) <;>
      cases cdiv c.P (KCBall.sub (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) cs.1) cs.2)
        (KCBall.mul c.P (KCBall.mulR c.P (piB c.P) z) z) <;> simp

end KNum
