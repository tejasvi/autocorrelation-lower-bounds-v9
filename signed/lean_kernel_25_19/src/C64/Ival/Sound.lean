import Mathlib
import C64Core.Ival

/-!
# Soundness of the ball arithmetic of `C64.Ival.Core`

`mem P x a` says that the real number `x` lies in the ball `a` at precision `P`.
-/

namespace Ival.Ball

open Real

/-- `x` lies in the ball `a` at precision `P`. -/
def mem (P : ℕ) (x : ℝ) (a : Ball) : Prop := |x - (a.m : ℝ) / 2 ^ P| ≤ (a.r : ℝ) / 2 ^ P

section rounding

theorem rnd2_spec (p : ℤ) (k : ℕ) : |(p : ℝ) / 2 ^ k - (rnd2 p k : ℝ)| ≤ 1 := by
  unfold rnd2
  set D : ℤ := ((2 ^ k : ℕ) : ℤ) with hD
  set h : ℤ := ((2 ^ k / 2 : ℕ) : ℤ) with hh
  have hDpos : 0 < D := by rw [hD]; positivity
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have hhD : h ≤ D := by
    simp only [hh, hD]; exact_mod_cast Nat.div_le_self _ _
  set q := (p + h) / D with hq
  have h1 : q * D ≤ p + h := Int.ediv_mul_le _ hDpos.ne'
  have h2 : p + h < (q + 1) * D := by
    have := Int.lt_ediv_add_one_mul_self (p + h) hDpos
    linarith
  have hDr : (D : ℝ) = 2 ^ k := by simp [hD]
  have hDr0 : (0 : ℝ) < D := by exact_mod_cast hDpos
  rw [← hDr, abs_le]
  have e1 : ((q : ℝ) * D) ≤ p + h := by exact_mod_cast h1
  have e2 : (p : ℝ) + h < (q + 1) * D := by exact_mod_cast h2
  have e3 : (0 : ℝ) ≤ h := by exact_mod_cast hh0
  have e4 : (h : ℝ) ≤ D := by exact_mod_cast hhD
  constructor
  · rw [le_sub_iff_add_le, ← sub_eq_neg_add, sub_le_iff_le_add, div_add_one hDr0.ne', le_div_iff₀ hDr0]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hDr0]
    nlinarith

theorem rndN_spec (p : ℤ) (d : ℕ) (hd : 0 < d) : |(p : ℝ) / d - (rndN p d : ℝ)| ≤ 1 := by
  unfold rndN
  set D : ℤ := (d : ℤ) with hD
  set h : ℤ := ((d / 2 : ℕ) : ℤ) with hh
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast hd
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have hhD : h ≤ D := by
    simp only [hh, hD]; exact_mod_cast Nat.div_le_self _ _
  set q := (p + h) / D with hq
  have h1 : q * D ≤ p + h := Int.ediv_mul_le _ hDpos.ne'
  have h2 : p + h < (q + 1) * D := by
    have := Int.lt_ediv_add_one_mul_self (p + h) hDpos
    linarith
  have hDr : (D : ℝ) = d := by simp [hD]
  have hDr0 : (0 : ℝ) < D := by exact_mod_cast hDpos
  rw [← hDr, abs_le]
  have e1 : ((q : ℝ) * D) ≤ p + h := by exact_mod_cast h1
  have e2 : (p : ℝ) + h < (q + 1) * D := by exact_mod_cast h2
  have e3 : (0 : ℝ) ≤ h := by exact_mod_cast hh0
  have e4 : (h : ℝ) ≤ D := by exact_mod_cast hhD
  constructor
  · rw [le_sub_iff_add_le, ← sub_eq_neg_add, sub_le_iff_le_add, div_add_one hDr0.ne', le_div_iff₀ hDr0]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hDr0]
    nlinarith

theorem cdiv_spec (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ (cdiv n d : ℝ) := by
  unfold cdiv
  have h : n ≤ (n + d - 1) / d * d := by
    have := Nat.lt_div_mul_add (a := n + d - 1) hd
    omega
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast h

end rounding

variable {P : ℕ}

theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < 2 ^ P := by positivity

theorem mem_ofInt (P : ℕ) (n : ℤ) : mem P (n : ℝ) (ofInt P n) := by
  unfold mem ofInt
  simp only [Nat.cast_zero, zero_div]
  have : ((n * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P = n := by
    push_cast; field_simp
  rw [this, sub_self, abs_zero]

theorem mem_ofRat (P : ℕ) (num : ℤ) (den : ℕ) (hd : 0 < den) :
    mem P ((num : ℝ) / den) (ofRat P num den) := by
  unfold mem ofRat
  have h := rndN_spec (num * ((2 ^ P : ℕ) : ℤ)) den hd
  have hP := two_pow_pos' P
  have e : ((num : ℝ) / den) - (rndN (num * ((2 ^ P : ℕ) : ℤ)) den : ℝ) / 2 ^ P
      = ((((num * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / den) - (rndN (num * ((2 ^ P : ℕ) : ℤ)) den : ℝ)) / 2 ^ P := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hP]
  simp only [Nat.cast_one]
  exact div_le_div_of_nonneg_right h hP.le

theorem mem_add {x y : ℝ} {a b : Ball} (ha : mem P x a) (hb : mem P y b) : mem P (x + y) (add a b) := by
  unfold mem add at *
  push_cast
  have e : x + y - ((a.m : ℝ) + b.m) / 2 ^ P = (x - a.m / 2 ^ P) + (y - b.m / 2 ^ P) := by ring
  rw [e, add_div]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

theorem mem_neg {x : ℝ} {a : Ball} (ha : mem P x a) : mem P (-x) (neg a) := by
  unfold mem neg at *
  push_cast
  have e : -x - -(a.m : ℝ) / 2 ^ P = -(x - a.m / 2 ^ P) := by ring
  rw [e, abs_neg]; exact ha

theorem mem_sub {x y : ℝ} {a b : Ball} (ha : mem P x a) (hb : mem P y b) : mem P (x - y) (sub a b) := by
  unfold mem sub at *
  push_cast
  have e : x - y - ((a.m : ℝ) - b.m) / 2 ^ P = (x - a.m / 2 ^ P) - (y - b.m / 2 ^ P) := by ring
  rw [e, add_div]
  exact (abs_sub _ _).trans (add_le_add ha hb)

theorem mem_mulInt {x : ℝ} {a : Ball} (n : ℤ) (ha : mem P x a) : mem P (n * x) (mulInt n a) := by
  unfold mem mulInt at *
  push_cast
  have e : (n : ℝ) * x - (n : ℝ) * a.m / 2 ^ P = n * (x - a.m / 2 ^ P) := by ring
  rw [e, abs_mul, Nat.cast_natAbs, Int.cast_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)

theorem mem_mul {x y : ℝ} {a b : Ball} (ha : mem P x a) (hb : mem P y b) :
    mem P (x * y) (mul P a b) := by
  unfold mem mul at *
  have hP := two_pow_pos' P
  set A : ℝ := a.m / 2 ^ P
  set B : ℝ := b.m / 2 ^ P
  set ra : ℝ := a.r / 2 ^ P
  set rb : ℝ := b.r / 2 ^ P
  -- |xy - AB| ≤ |A| rb + |B| ra + ra rb
  have key : |x * y - A * B| ≤ |A| * rb + |B| * ra + ra * rb := by
    have e : x * y - A * B = (x - A) * (y - B) + A * (y - B) + B * (x - A) := by ring
    rw [e]
    calc |(x - A) * (y - B) + A * (y - B) + B * (x - A)|
        ≤ |(x - A) * (y - B)| + |A * (y - B)| + |B * (x - A)| := abs_add_three _ _ _
      _ = |x - A| * |y - B| + |A| * |y - B| + |B| * |x - A| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ ra * rb + |A| * rb + |B| * ra := by
          gcongr
      _ = |A| * rb + |B| * ra + ra * rb := by ring
  -- the bound in units
  set N : ℕ := a.m.natAbs * b.r + b.m.natAbs * a.r + a.r * b.r
  have hN : |A| * rb + |B| * ra + ra * rb = ((N : ℝ) / 2 ^ P) / 2 ^ P := by
    simp only [N, A, B, ra, rb, abs_div, abs_of_pos hP]
    push_cast
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    field_simp
  have hc := cdiv_spec N (2 ^ P) (by positivity)
  have hr := rnd2_spec (a.m * b.m) P
  have hAB : A * B = (((a.m * b.m : ℤ) : ℝ) / 2 ^ P) / 2 ^ P := by
    simp only [A, B]; push_cast; field_simp
  have e2 : x * y - (rnd2 (a.m * b.m) P : ℝ) / 2 ^ P
      = (x * y - A * B) + ((((a.m * b.m : ℤ) : ℝ) / 2 ^ P) - (rnd2 (a.m * b.m) P : ℝ)) / 2 ^ P := by
    rw [hAB]; field_simp; ring
  rw [e2]
  calc |(x * y - A * B) + ((((a.m * b.m : ℤ) : ℝ) / 2 ^ P) - (rnd2 (a.m * b.m) P : ℝ)) / 2 ^ P|
      ≤ |x * y - A * B| + |((((a.m * b.m : ℤ) : ℝ) / 2 ^ P) - (rnd2 (a.m * b.m) P : ℝ)) / 2 ^ P| :=
        abs_add_le _ _
    _ ≤ ((N : ℝ) / 2 ^ P) / 2 ^ P + 1 / 2 ^ P := by
        gcongr
        · exact key.trans hN.le
        · rw [abs_div, abs_of_pos hP]; exact div_le_div_of_nonneg_right hr hP.le
    _ ≤ (cdiv N (2 ^ P) : ℝ) / 2 ^ P + 1 / 2 ^ P := by
        gcongr
        exact_mod_cast hc
    _ = ((cdiv N (2 ^ P) + 1 : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

theorem mem_shr {x : ℝ} {a : Ball} (k : ℕ) (ha : mem P x a) : mem P (x / 2 ^ k) (shr k a) := by
  unfold mem shr at *
  have hP := two_pow_pos' P
  have hk := two_pow_pos' k
  have hc := cdiv_spec a.r (2 ^ k) (by positivity)
  have hr := rnd2_spec a.m k
  have e : x / 2 ^ k - (rnd2 a.m k : ℝ) / 2 ^ P
      = (x - a.m / 2 ^ P) / 2 ^ k + (((a.m : ℝ) / 2 ^ k) - (rnd2 a.m k : ℝ)) / 2 ^ P := by
    field_simp; ring
  rw [e]
  calc |(x - a.m / 2 ^ P) / 2 ^ k + (((a.m : ℝ) / 2 ^ k) - (rnd2 a.m k : ℝ)) / 2 ^ P|
      ≤ |(x - a.m / 2 ^ P) / 2 ^ k| + |(((a.m : ℝ) / 2 ^ k) - (rnd2 a.m k : ℝ)) / 2 ^ P| :=
        abs_add_le _ _
    _ ≤ ((a.r : ℝ) / 2 ^ P) / 2 ^ k + 1 / 2 ^ P := by
        rw [abs_div, abs_div, abs_of_pos hP, abs_of_pos hk]
        gcongr
    _ = ((a.r : ℝ) / 2 ^ k) / 2 ^ P + 1 / 2 ^ P := by ring
    _ ≤ (cdiv a.r (2 ^ k) : ℝ) / 2 ^ P + 1 / 2 ^ P := by
        gcongr
        exact_mod_cast hc
    _ = ((cdiv a.r (2 ^ k) + 1 : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

theorem mem_divNat {x : ℝ} {a : Ball} {d : ℕ} (hd : 0 < d) (ha : mem P x a) :
    mem P (x / d) (divNat d a) := by
  unfold mem divNat at *
  have hP := two_pow_pos' P
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := cdiv_spec a.r d hd
  have hr := rndN_spec a.m d hd
  have e : x / d - (rndN a.m d : ℝ) / 2 ^ P
      = (x - a.m / 2 ^ P) / d + (((a.m : ℝ) / d) - (rndN a.m d : ℝ)) / 2 ^ P := by
    field_simp; ring
  rw [e]
  calc |(x - a.m / 2 ^ P) / d + (((a.m : ℝ) / d) - (rndN a.m d : ℝ)) / 2 ^ P|
      ≤ |(x - a.m / 2 ^ P) / d| + |(((a.m : ℝ) / d) - (rndN a.m d : ℝ)) / 2 ^ P| := abs_add_le _ _
    _ ≤ ((a.r : ℝ) / 2 ^ P) / d + 1 / 2 ^ P := by
        rw [abs_div, abs_div, abs_of_pos hP, abs_of_pos hd']
        gcongr
    _ = ((a.r : ℝ) / d) / 2 ^ P + 1 / 2 ^ P := by ring
    _ ≤ (cdiv a.r d : ℝ) / 2 ^ P + 1 / 2 ^ P := by
        gcongr
    _ = ((cdiv a.r d + 1 : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

/-- `|x| ≤ absHi a / 2^P` on the ball. -/
theorem abs_le_absHi {x : ℝ} {a : Ball} (ha : mem P x a) : |x| ≤ (a.absHi : ℝ) / 2 ^ P := by
  unfold mem at ha
  unfold absHi
  have hP := two_pow_pos' P
  have h1 : |x| ≤ |(a.m : ℝ) / 2 ^ P| + (a.r : ℝ) / 2 ^ P := by
    have := abs_sub_abs_le_abs_sub x ((a.m : ℝ) / 2 ^ P)
    linarith
  rw [abs_div, abs_of_pos hP] at h1
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, add_div]
  exact h1

theorem isPos_sound {x : ℝ} {a : Ball} (ha : mem P x a) (h : a.isPos = true) : 0 < x := by
  unfold isPos at h
  unfold mem at ha
  have h' : (a.r : ℤ) < a.m := by simpa using h
  have hP := two_pow_pos' P
  have h2 : ((a.r : ℝ)) < a.m := by exact_mod_cast h'
  have h3 := (abs_le.mp ha).1
  have : (0 : ℝ) < (a.m : ℝ) / 2 ^ P - (a.r : ℝ) / 2 ^ P := by
    rw [← sub_div]; exact div_pos (by linarith) hP
  linarith

theorem isNeg_sound {x : ℝ} {a : Ball} (ha : mem P x a) (h : a.isNeg = true) : x < 0 := by
  unfold isNeg at h
  unfold mem at ha
  have h' : a.m + (a.r : ℤ) < 0 := by simpa using h
  have hP := two_pow_pos' P
  have h2 : (a.m : ℝ) + a.r < 0 := by exact_mod_cast h'
  have h3 := (abs_le.mp ha).2
  have : (a.m : ℝ) / 2 ^ P + (a.r : ℝ) / 2 ^ P < 0 := by
    rw [← add_div]; exact div_neg_of_neg_of_pos h2 hP
  linarith


/-! ## Taylor sums -/

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, Nat.factorial, ih]

/-- The sign of the `i`-th Taylor term of `cos`/`sin` (`alt = true`), or `1` (`alt = false`). -/
noncomputable def sgn (alt : Bool) (i : ℕ) : ℝ := if alt = true ∧ 2 ≤ i % 4 then -1 else 1

/-- Even part of the (signed) exponential series up to `j`. -/
noncomputable def evSum (alt : Bool) (ξ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, if i % 2 = 0 then sgn alt i * (ξ ^ i / i.factorial) else 0

/-- Odd part of the (signed) exponential series up to `j`. -/
noncomputable def odSum (alt : Bool) (ξ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, if i % 2 = 1 then sgn alt i * (ξ ^ i / i.factorial) else 0

theorem mem_taylorAux {ξ : ℝ} {X : Ball} (hX : mem P ξ X) (alt : Bool) :
    ∀ (fuel j : ℕ) (t ev od : Ball), mem P (ξ ^ j / j.factorial) t → mem P (evSum alt ξ j) ev →
      mem P (odSum alt ξ j) od →
      mem P (evSum alt ξ (j + fuel)) (taylorAux P alt X fuel j t ev od).1 ∧
      mem P (odSum alt ξ (j + fuel)) (taylorAux P alt X fuel j t ev od).2 := by
  intro fuel
  induction fuel with
  | zero => intro j t ev od _ he ho; exact ⟨he, ho⟩
  | succ fuel ih =>
    intro j t ev od ht he ho
    simp only [taylorAux]
    have ht' : mem P (ξ ^ (j + 1) / (j + 1).factorial) (divNat (j + 1) (mul P t X)) := by
      have h1 := mem_divNat (Nat.succ_pos j) (mem_mul ht hX)
      have e : ξ ^ j / j.factorial * ξ / ((j + 1 : ℕ) : ℝ) = ξ ^ (j + 1) / (j + 1).factorial := by
        rw [Nat.factorial_succ]; push_cast; field_simp; ring
      rw [e] at h1; exact h1
    have hev : evSum alt ξ (j + 1) = evSum alt ξ j +
        (if j % 2 = 0 then sgn alt j * (ξ ^ j / j.factorial) else 0) := by
      simp [evSum, Finset.sum_range_succ]
    have hod : odSum alt ξ (j + 1) = odSum alt ξ j +
        (if j % 2 = 1 then sgn alt j * (ξ ^ j / j.factorial) else 0) := by
      simp [odSum, Finset.sum_range_succ]
    have he' : mem P (evSum alt ξ (j + 1))
        (if j % 2 == 0 then (if alt && j % 4 == 2 then sub ev t else add ev t) else ev) := by
      rw [hev]
      by_cases h2 : j % 2 = 0
      · have h4 : j % 4 = 0 ∨ j % 4 = 2 := by omega
        by_cases hs : alt = true ∧ j % 4 = 2
        · obtain ⟨rfl, h42⟩ := hs
          have hsg : sgn true j = -1 := by simp [sgn]; omega
          simp only [h2, h42, beq_self_eq_true, ite_true, Bool.and_self]
          rw [hsg, neg_one_mul, ← sub_eq_add_neg]
          exact mem_sub he ht
        · have : sgn alt j = 1 := by
            simp only [sgn]; split_ifs with hh
            · exfalso; apply hs; refine ⟨hh.1, ?_⟩; omega
            · rfl
          have hb : (alt && j % 4 == 2) = false := by
            cases alt <;> simp_all
          simp only [h2, beq_self_eq_true, ite_true, hb, this, one_mul]
          exact mem_add he ht
      · have h2' : (j % 2 == 0) = false := by simp [h2]
        simp only [h2, h2', ite_false, add_zero]
        exact he
    have ho' : mem P (odSum alt ξ (j + 1))
        (if j % 2 == 1 then (if alt && j % 4 == 3 then sub od t else add od t) else od) := by
      rw [hod]
      by_cases h2 : j % 2 = 1
      · by_cases hs : alt = true ∧ j % 4 = 3
        · obtain ⟨rfl, h43⟩ := hs
          have hsg : sgn true j = -1 := by simp [sgn]; omega
          simp only [h2, h43, beq_self_eq_true, ite_true, Bool.and_self]
          rw [hsg, neg_one_mul, ← sub_eq_add_neg]
          exact mem_sub ho ht
        · have : sgn alt j = 1 := by
            simp only [sgn]; split_ifs with hh
            · exfalso; apply hs; refine ⟨hh.1, ?_⟩; omega
            · rfl
          have hb : (alt && j % 4 == 3) = false := by
            cases alt <;> simp_all
          simp only [h2, beq_self_eq_true, ite_true, hb, this, one_mul]
          exact mem_add ho ht
      · have h2' : (j % 2 == 1) = false := by simp [h2]
        simp only [h2, h2', ite_false, add_zero]
        exact ho
    have := ih (j + 1) _ _ _ ht' he' ho'
    rw [show j + 1 + fuel = j + (fuel + 1) by ring] at this
    exact this

theorem evSum_add_odSum_false (ξ : ℝ) (n : ℕ) :
    evSum false ξ n + odSum false ξ n = ∑ i ∈ Finset.range n, ξ ^ i / i.factorial := by
  rw [evSum, odSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hs : sgn false i = 1 := by simp [sgn]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, hs]

theorem mem_zero_ball : mem P (0 : ℝ) (⟨0, 0⟩ : Ball) := by
  simp [mem]

/-- The remainder bound dominates `|ξ|^n (n+1)/(n! n)`. -/
theorem rem_le {ξ : ℝ} {X : Ball} (hX : mem P ξ X) {n : ℕ} (hn : 0 < n) (h1 : X.absHi ≤ 2 ^ P) :
    |ξ| ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ (remBound P n X.absHi : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have habs := abs_le_absHi hX
  have hden : (0 : ℝ) < (fact n * n * 2 ^ (P * (n - 1)) : ℕ) := by
    rw [fact_eq]; positivity
  have hc := cdiv_spec (X.absHi ^ n * (n + 1)) (fact n * n * 2 ^ (P * (n - 1))) (by exact_mod_cast hden)
  unfold remBound
  calc |ξ| ^ n * ((n.succ : ℝ) / (n.factorial * n))
      ≤ ((X.absHi : ℝ) / 2 ^ P) ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by
        gcongr
    _ = (((X.absHi ^ n * (n + 1) : ℕ) : ℝ) / ((fact n * n * 2 ^ (P * (n - 1)) : ℕ) : ℝ)) / 2 ^ P := by
        rw [fact_eq]
        push_cast
        have : (2 : ℝ) ^ (P * (n - 1)) * 2 ^ P = (2 ^ P) ^ n := by
          rw [← pow_mul, ← pow_add]
          congr 1
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp; ring
        rw [div_pow]
        field_simp
        rw [← this]; ring
    _ ≤ (cdiv (X.absHi ^ n * (n + 1)) (fact n * n * 2 ^ (P * (n - 1))) : ℝ) / 2 ^ P := by
        gcongr

theorem mem_expSmall {ξ : ℝ} {X E : Ball} {n : ℕ} (hX : mem P ξ X) (h : expSmall P n X = some E) :
    mem P (Real.exp ξ) E := by
  unfold expSmall at h
  split_ifs at h with hc
  obtain ⟨h1, hn⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have hT := mem_taylorAux hX false n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
    (by simpa using mem_ofInt P 1) (by simp [evSum, mem]) (by simp [odSum, mem])
  rw [zero_add] at hT
  have hS := mem_add hT.1 hT.2
  rw [evSum_add_odSum_false] at hS
  have hP := two_pow_pos' P
  have habs : |ξ| ≤ 1 := by
    have := abs_le_absHi hX
    have h2 : (X.absHi : ℝ) / 2 ^ P ≤ 1 := by
      rw [div_le_one hP]; exact_mod_cast h1
    linarith
  have hb := Real.exp_bound habs hn
  have hr := rem_le hX hn h1
  unfold mem at hS ⊢
  set S := ∑ i ∈ Finset.range n, ξ ^ i / i.factorial
  set T := taylorAux P false X n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
  push_cast
  calc |Real.exp ξ - ((add T.1 T.2).m : ℝ) / 2 ^ P|
      ≤ |Real.exp ξ - S| + |S - ((add T.1 T.2).m : ℝ) / 2 ^ P| := abs_sub_le _ _ _
    _ ≤ (remBound P n X.absHi : ℝ) / 2 ^ P + ((add T.1 T.2).r : ℝ) / 2 ^ P := by
        gcongr
        exact hb.trans hr
    _ = (((add T.1 T.2).r : ℝ) + remBound P n X.absHi) / 2 ^ P := by ring

theorem mem_sqIter {y : ℝ} {E : Ball} (hE : mem P (Real.exp y) E) :
    ∀ k : ℕ, mem P (Real.exp (y * 2 ^ k)) (sqIter P k E) := by
  intro k
  induction k generalizing y E with
  | zero => simpa [sqIter] using hE
  | succ k ih =>
    simp only [sqIter]
    have h2 : mem P (Real.exp (2 * y)) (mul P E E) := by
      have := mem_mul hE hE
      rwa [← Real.exp_add, ← two_mul] at this
    have := ih h2
    rwa [show 2 * y * 2 ^ k = y * 2 ^ (k + 1) by rw [pow_succ]; ring] at this

theorem mem_expB {ξ : ℝ} {X E : Ball} {n : ℕ} (hX : mem P ξ X) (h : expB P n X = some E) :
    mem P (Real.exp ξ) E := by
  cases he : expSmall P n (shr (findShift P X.absHi 64 0) X) with
  | none => simp [expB, he] at h
  | some e =>
    simp only [expB, he, Option.some.injEq] at h
    subst h
    have h1 := mem_expSmall (mem_shr (findShift P X.absHi 64 0) hX) he
    have := mem_sqIter h1 (findShift P X.absHi 64 0)
    rwa [div_mul_cancel₀ _ (by positivity)] at this

theorem exp_neg_le_two_pow (P : ℕ) : Real.exp (-(P : ℝ)) ≤ 1 / 2 ^ P := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : (2 : ℝ) ^ P ≤ Real.exp (P : ℝ) := by
    calc (2 : ℝ) ^ P ≤ (Real.exp 1) ^ P := pow_le_pow_left₀ (by norm_num) h2 _
      _ = Real.exp (P : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) h3

theorem mem_expB' {ξ : ℝ} {X E : Ball} {n : ℕ} (hX : mem P ξ X) (h : expB' P n X = some E) :
    mem P (Real.exp ξ) E := by
  unfold expB' at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    subst h
    unfold mem
    simp only [Int.cast_zero, zero_div, sub_zero, Nat.cast_one]
    have hp := two_pow_pos' P
    have hx : ξ ≤ -(P : ℝ) := by
      unfold mem at hX
      have h1 := (abs_le.mp hX).2
      unfold hi at hc
      have h2 : ((X.m + (X.r : ℤ) : ℤ) : ℝ) ≤ ((-((P : ℤ) * ((2 ^ P : ℕ) : ℤ)) : ℤ) : ℝ) := by
        exact_mod_cast hc
      push_cast at h2
      have h3 : (X.m : ℝ) / 2 ^ P + (X.r : ℝ) / 2 ^ P ≤ -(P : ℝ) := by
        rw [← add_div, div_le_iff₀ hp]; linarith
      linarith
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_exp.mpr hx).trans (exp_neg_le_two_pow P)
  · exact mem_expB hX h

theorem mem_point' (P : ℕ) (y0 : ℤ) : mem P ((y0 : ℝ) / 2 ^ P) (⟨y0, 0⟩ : Ball) := by
  simp [mem]

theorem mem_iff_lo_hi {x : ℝ} {a : Ball} :
    mem P x a ↔ (a.lo : ℝ) / 2 ^ P ≤ x ∧ x ≤ (a.hi : ℝ) / 2 ^ P := by
  unfold mem lo hi
  have hP := two_pow_pos' P
  rw [abs_le]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [sub_div]; linarith
    · rw [add_div]; linarith
  · rintro ⟨h1, h2⟩
    constructor
    · rw [sub_div] at h1; linarith
    · rw [add_div] at h2; linarith

theorem mem_hullB {x : ℝ} {a b : Ball} (h1 : ((min a.lo b.lo : ℤ) : ℝ) / 2 ^ P ≤ x)
    (h2 : x ≤ ((max a.hi b.hi : ℤ) : ℝ) / 2 ^ P) : mem P x (hullB a b) := by
  rw [mem_iff_lo_hi]
  unfold hullB lo hi
  simp only
  set l := min a.lo b.lo
  set h := max a.hi b.hi
  set m := (l + h) / 2
  have hP := two_pow_pos' P
  have hm1 : m - l ≤ ((max (h - m) (m - l)).toNat : ℤ) := (le_max_right _ _).trans (Int.self_le_toNat _)
  have hm2 : h - m ≤ ((max (h - m) (m - l)).toNat : ℤ) := (le_max_left _ _).trans (Int.self_le_toNat _)
  constructor
  · have : ((m - ((max (h - m) (m - l)).toNat : ℤ) : ℤ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by linarith)
    calc ((m - ((max (h - m) (m - l)).toNat : ℤ) : ℤ) : ℝ) / 2 ^ P ≤ (l : ℝ) / 2 ^ P :=
          div_le_div_of_nonneg_right this hP.le
      _ ≤ x := h1
  · have : (h : ℝ) ≤ ((m + ((max (h - m) (m - l)).toNat : ℤ) : ℤ) : ℝ) := by exact_mod_cast (by linarith)
    calc x ≤ (h : ℝ) / 2 ^ P := h2
      _ ≤ ((m + ((max (h - m) (m - l)).toNat : ℤ) : ℤ) : ℝ) / 2 ^ P :=
          div_le_div_of_nonneg_right this hP.le

theorem mem_expH {ξ : ℝ} {X E : Ball} {n : ℕ} (hX : mem P ξ X) (h : expH P n X = some E) :
    mem P (Real.exp ξ) E := by
  simp only [expH, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨e1, he1, e2, he2, rfl⟩ := h
  have hP := two_pow_pos' P
  have hlo := mem_expB' (mem_point' P (X.m - X.r)) he1
  have hhi := mem_expB' (mem_point' P (X.m + X.r)) he2
  rw [mem_iff_lo_hi] at hX hlo hhi
  unfold lo hi at hX
  push_cast at hX
  apply mem_hullB
  · have h1 : ((min e1.lo e2.lo : ℤ) : ℝ) ≤ e1.lo := by exact_mod_cast min_le_left _ _
    have h2 : Real.exp (((X.m - X.r : ℤ) : ℝ) / 2 ^ P) ≤ Real.exp ξ := by
      apply Real.exp_le_exp.mpr; push_cast; rw [sub_div] at hX ⊢; linarith [hX.1]
    calc ((min e1.lo e2.lo : ℤ) : ℝ) / 2 ^ P ≤ (e1.lo : ℝ) / 2 ^ P := div_le_div_of_nonneg_right h1 hP.le
      _ ≤ Real.exp (((X.m - X.r : ℤ) : ℝ) / 2 ^ P) := hlo.1
      _ ≤ Real.exp ξ := h2
  · have h1 : (e2.hi : ℝ) ≤ ((max e1.hi e2.hi : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h2 : Real.exp ξ ≤ Real.exp (((X.m + X.r : ℤ) : ℝ) / 2 ^ P) := by
      apply Real.exp_le_exp.mpr; push_cast; rw [add_div] at hX ⊢; linarith [hX.2]
    calc Real.exp ξ ≤ Real.exp (((X.m + X.r : ℤ) : ℝ) / 2 ^ P) := h2
      _ ≤ (e2.hi : ℝ) / 2 ^ P := hhi.2
      _ ≤ ((max e1.hi e2.hi : ℤ) : ℝ) / 2 ^ P := div_le_div_of_nonneg_right h1 hP.le

theorem mem_absB {x : ℝ} {a : Ball} (ha : mem P x a) : mem P |x| (absB a) := by
  unfold mem absB at *
  have e : ((a.m.natAbs : ℤ) : ℝ) = |(a.m : ℝ)| := by rw [Int.cast_natCast, Nat.cast_natAbs, Int.cast_abs]
  simp only
  rw [e, ← abs_of_pos (two_pow_pos' P), ← abs_div, abs_of_pos (two_pow_pos' P)]
  exact (abs_abs_sub_abs_le_abs_sub x _).trans ha

/-! ## π -/

theorem mem_piB (P : ℕ) : mem P π (piB P) := by
  unfold mem piB
  have hP := two_pow_pos' P
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  set c : ℝ := (628318530717958647693 : ℝ) / (2 * 10 ^ 20)
  have hc : |π - c| ≤ 1 / (2 * 10 ^ 20) := by
    rw [abs_le]; constructor <;> norm_num [c] at hlo hhi ⊢ <;> linarith
  have hr := rndN_spec (628318530717958647693 * ((2 ^ P : ℕ) : ℤ)) (2 * 10 ^ 20) (by norm_num)
  have hcd := cdiv_spec (2 ^ P) (2 * 10 ^ 20) (by norm_num)
  set q := rndN (628318530717958647693 * ((2 ^ P : ℕ) : ℤ)) (2 * 10 ^ 20)
  have e : π - (q : ℝ) / 2 ^ P = (π - c) +
      ((((628318530717958647693 * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 10 ^ 20 : ℕ) : ℝ)) - (q : ℝ)) / 2 ^ P := by
    simp only [c]; push_cast; field_simp; ring
  rw [e]
  calc |(π - c) + ((((628318530717958647693 * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 10 ^ 20 : ℕ) : ℝ)) - (q : ℝ)) / 2 ^ P|
      ≤ |π - c| + |((((628318530717958647693 * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / ((2 * 10 ^ 20 : ℕ) : ℝ)) - (q : ℝ)) / 2 ^ P| :=
        abs_add_le _ _
    _ ≤ ((2 ^ P : ℕ) : ℝ) / ((2 * 10 ^ 20 : ℕ) : ℝ) / 2 ^ P + 1 / 2 ^ P := by
        gcongr
        · refine hc.trans (le_of_eq ?_); push_cast; field_simp; norm_num
        · rw [abs_div, abs_of_pos hP]; exact div_le_div_of_nonneg_right hr hP.le
    _ ≤ (cdiv (2 ^ P) (2 * 10 ^ 20) : ℝ) / 2 ^ P + 1 / 2 ^ P := by gcongr
    _ = ((cdiv (2 ^ P) (2 * 10 ^ 20) + 1 : ℕ) : ℝ) / 2 ^ P := by push_cast; ring

end Ival.Ball
