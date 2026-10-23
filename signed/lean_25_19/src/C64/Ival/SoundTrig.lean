import C64.Ival.Sound

/-!
# Soundness of `cos`/`sin` in turns
-/

namespace Ival.Ball

open Real

variable {P : ℕ}

/-! ## cos and sin -/

theorem I_pow_mod4 (m : ℕ) : Complex.I ^ m = Complex.I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem expSeries_I (θ : ℝ) (n : ℕ) :
    (∑ m ∈ Finset.range n, ((θ : ℂ) * Complex.I) ^ m / m.factorial).re = evSum true θ n ∧
    (∑ m ∈ Finset.range n, ((θ : ℂ) * Complex.I) ^ m / m.factorial).im = odSum true θ n := by
  have key : ∀ m : ℕ, ((θ : ℂ) * Complex.I) ^ m / m.factorial =
      ((θ ^ m / m.factorial : ℝ) : ℂ) * Complex.I ^ (m % 4) := by
    intro m; rw [mul_pow, I_pow_mod4]; push_cast; ring
  constructor
  · rw [Complex.re_sum, evSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [key m, Complex.re_ofReal_mul]
    have : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases this with h | h | h | h
    · have h2 : m % 2 = 0 := by omega
      simp [h, h2, sgn]
    · have h2 : m % 2 = 1 := by omega
      simp [h, h2]
    · have h2 : m % 2 = 0 := by omega
      simp [h, h2, sgn]
    · have h2 : m % 2 = 1 := by omega
      simp [h, h2, pow_succ, Complex.I_sq]
  · rw [Complex.im_sum, odSum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [key m, Complex.im_ofReal_mul]
    have : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases this with h | h | h | h
    · have h2 : m % 2 = 0 := by omega
      simp [h, h2]
    · have h2 : m % 2 = 1 := by omega
      simp [h, h2, sgn]
    · have h2 : m % 2 = 0 := by omega
      simp [h, h2, Complex.I_sq]
    · have h2 : m % 2 = 1 := by omega
      simp [h, h2, sgn, pow_succ, Complex.I_sq]

theorem mem_cosSinSmall {θ : ℝ} {Θ : Ball} {n : ℕ} {C S : Ball} (hΘ : mem P θ Θ)
    (h : cosSinSmall P n Θ = some (C, S)) : mem P (Real.cos θ) C ∧ mem P (Real.sin θ) S := by
  unfold cosSinSmall at h
  split_ifs at h with hc
  obtain ⟨h1, hn⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hC, hS⟩ := h
  subst hC hS
  have hT := mem_taylorAux hΘ true n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
    (by simpa using mem_ofInt P 1) (by simp [evSum, mem]) (by simp [odSum, mem])
  rw [zero_add] at hT
  have hP := two_pow_pos' P
  have habs : |θ| ≤ 1 := by
    have := abs_le_absHi hΘ
    have h2 : (Θ.absHi : ℝ) / 2 ^ P ≤ 1 := by
      rw [div_le_one hP]; exact_mod_cast h1
    linarith
  have hθI : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by simpa using habs
  have hb := Complex.exp_bound hθI hn
  rw [show ‖(θ : ℂ) * Complex.I‖ = |θ| by simp] at hb
  have hr := rem_le hΘ hn h1
  obtain ⟨hre, him⟩ := expSeries_I θ n
  set Z := Complex.exp ((θ : ℂ) * Complex.I) - ∑ m ∈ Finset.range n, ((θ : ℂ) * Complex.I) ^ m / m.factorial
  have hZre : Z.re = Real.cos θ - evSum true θ n := by
    simp only [Z, Complex.sub_re, Complex.exp_ofReal_mul_I_re, hre]
  have hZim : Z.im = Real.sin θ - odSum true θ n := by
    simp only [Z, Complex.sub_im, Complex.exp_ofReal_mul_I_im, him]
  have hbound : ‖Z‖ ≤ (remBound P n Θ.absHi : ℝ) / 2 ^ P := by
    calc ‖Z‖ ≤ |θ| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := hb
      _ = |θ| ^ n * ((n.succ : ℝ) / (n.factorial * n)) := by rw [div_eq_mul_inv]
      _ ≤ _ := hr
  set T := taylorAux P true Θ n 0 (ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩
  unfold mem at hT ⊢
  constructor
  · push_cast
    calc |Real.cos θ - (T.1.m : ℝ) / 2 ^ P|
        ≤ |Real.cos θ - evSum true θ n| + |evSum true θ n - (T.1.m : ℝ) / 2 ^ P| := abs_sub_le _ _ _
      _ ≤ (remBound P n Θ.absHi : ℝ) / 2 ^ P + (T.1.r : ℝ) / 2 ^ P := by
          gcongr
          · rw [← hZre]; exact (Complex.abs_re_le_norm Z).trans hbound
          · exact hT.1
      _ = ((T.1.r : ℝ) + remBound P n Θ.absHi) / 2 ^ P := by ring
  · push_cast
    calc |Real.sin θ - (T.2.m : ℝ) / 2 ^ P|
        ≤ |Real.sin θ - odSum true θ n| + |odSum true θ n - (T.2.m : ℝ) / 2 ^ P| := abs_sub_le _ _ _
      _ ≤ (remBound P n Θ.absHi : ℝ) / 2 ^ P + (T.2.r : ℝ) / 2 ^ P := by
          gcongr
          · rw [← hZim]; exact (Complex.abs_im_le_norm Z).trans hbound
          · exact hT.2
      _ = ((T.2.r : ℝ) + remBound P n Θ.absHi) / 2 ^ P := by ring

theorem mem_dblIter {y : ℝ} {cs : Ball × Ball} (hc : mem P (Real.cos y) cs.1)
    (hs : mem P (Real.sin y) cs.2) :
    ∀ k : ℕ, mem P (Real.cos (y * 2 ^ k)) (dblIter P k cs).1 ∧
      mem P (Real.sin (y * 2 ^ k)) (dblIter P k cs).2 := by
  intro k
  induction k generalizing y cs with
  | zero => simpa [dblIter] using ⟨hc, hs⟩
  | succ k ih =>
    obtain ⟨c, s⟩ := cs
    simp only [dblIter]
    have hc2 : mem P (Real.cos (2 * y)) (sub (mul P c c) (mul P s s)) := by
      rw [Real.cos_two_mul', sq, sq]; exact mem_sub (mem_mul hc hc) (mem_mul hs hs)
    have hs2 : mem P (Real.sin (2 * y)) (mulInt 2 (mul P c s)) := by
      have h2 := mem_mulInt 2 (mem_mul hc hs)
      have e : Real.sin (2 * y) = ((2 : ℤ) : ℝ) * (Real.cos y * Real.sin y) := by
        rw [Real.sin_two_mul]; push_cast; ring
      rw [e]; exact h2
    have := ih (y := 2 * y) (cs := (sub (mul P c c) (mul P s s), mulInt 2 (mul P c s))) hc2 hs2
    rwa [show 2 * y * 2 ^ k = y * 2 ^ (k + 1) by rw [pow_succ]; ring] at this

theorem mem_fracTurn {ξ : ℝ} {U : Ball} (hU : mem P ξ U) :
    mem P (ξ - rnd2 U.m P) (fracTurn P U) := by
  unfold mem fracTurn at *
  have e : ξ - (rnd2 U.m P : ℝ) - ((U.m - rnd2 U.m P * ((2 ^ P : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P
      = ξ - (U.m : ℝ) / 2 ^ P := by
    push_cast; field_simp; ring
  simp only
  rw [e]; exact hU

theorem mem_turnArg {ξ : ℝ} {U : Ball} (k : ℕ) (hU : mem P ξ U) :
    mem P ((2 * π * (ξ - rnd2 U.m P)) / 2 ^ k) (turnArg P k U) := by
  have h := mem_shr k (mem_mul (mem_mulInt 2 (mem_piB P)) (mem_fracTurn hU))
  have e : (2 * π * (ξ - rnd2 U.m P)) / 2 ^ k = ((2 : ℤ) : ℝ) * π * (ξ - rnd2 U.m P) / 2 ^ k := by
    push_cast; ring
  rw [e]; exact h

theorem mem_cosSinTurn {ξ : ℝ} {U : Ball} {n k : ℕ} {C S : Ball} (hU : mem P ξ U)
    (h : cosSinTurn P n k U = some (C, S)) :
    mem P (Real.cos (2 * π * ξ)) C ∧ mem P (Real.sin (2 * π * ξ)) S := by
  unfold cosSinTurn at h
  obtain ⟨⟨c0, s0⟩, hcs, h'⟩ := Option.map_eq_some_iff.mp h
  have h0 := mem_cosSinSmall (mem_turnArg k hU) hcs
  have h1 := mem_dblIter (cs := (c0, s0)) h0.1 h0.2 k
  rw [h'] at h1
  have e : (2 * π * (ξ - rnd2 U.m P)) / 2 ^ k * 2 ^ k
      = 2 * π * ξ - ((rnd2 U.m P : ℤ) : ℝ) * (2 * π) := by
    field_simp; try ring
  rw [e, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi] at h1
  exact h1

theorem mem_cosSinTurnC {ξ : ℝ} {U : Ball} {n k : ℕ} {C S : Ball} (hU : mem P ξ U)
    (h : cosSinTurnC P n k U = some (C, S)) :
    mem P (Real.cos (2 * π * ξ)) C ∧ mem P (Real.sin (2 * π * ξ)) S := by
  unfold cosSinTurnC at h
  obtain ⟨⟨c0, s0⟩, hcs, h'⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have hc := mem_cosSinTurn (mem_point' P U.m) hcs
  have hP := two_pow_pos' P
  set u : ℝ := (U.m : ℝ) / 2 ^ P
  have hd : |2 * π * ξ - 2 * π * u| ≤ ((cdiv (U.r * 62832) 10000 : ℕ) : ℝ) / 2 ^ P := by
    unfold mem at hU
    have h1 : |2 * π * ξ - 2 * π * u| = 2 * π * |ξ - u| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    have h2 : 2 * π ≤ 62832 / 10000 := by linarith [Real.pi_lt_d6]
    have h3 := cdiv_spec (U.r * 62832) 10000 (by norm_num)
    push_cast at h3
    rw [h1]
    calc 2 * π * |ξ - u| ≤ (62832 / 10000) * ((U.r : ℝ) / 2 ^ P) :=
          mul_le_mul h2 hU (abs_nonneg _) (by norm_num)
      _ = ((U.r : ℝ) * 62832 / 10000) / 2 ^ P := by ring
      _ ≤ ((cdiv (U.r * 62832) 10000 : ℕ) : ℝ) / 2 ^ P := div_le_div_of_nonneg_right h3 hP.le
  unfold mem at hc ⊢
  obtain ⟨hc1, hc2⟩ := hc
  constructor
  · push_cast
    calc |Real.cos (2 * π * ξ) - (c0.m : ℝ) / 2 ^ P|
        ≤ |Real.cos (2 * π * ξ) - Real.cos (2 * π * u)| + |Real.cos (2 * π * u) - (c0.m : ℝ) / 2 ^ P| :=
          abs_sub_le _ _ _
      _ ≤ ((cdiv (U.r * 62832) 10000 : ℕ) : ℝ) / 2 ^ P + (c0.r : ℝ) / 2 ^ P := by
          gcongr
          exact (Real.abs_cos_sub_cos_le _ _).trans hd
      _ = ((c0.r : ℝ) + (cdiv (U.r * 62832) 10000 : ℕ)) / 2 ^ P := by ring
  · push_cast
    calc |Real.sin (2 * π * ξ) - (s0.m : ℝ) / 2 ^ P|
        ≤ |Real.sin (2 * π * ξ) - Real.sin (2 * π * u)| + |Real.sin (2 * π * u) - (s0.m : ℝ) / 2 ^ P| :=
          abs_sub_le _ _ _
      _ ≤ ((cdiv (U.r * 62832) 10000 : ℕ) : ℝ) / 2 ^ P + (s0.r : ℝ) / 2 ^ P := by
          gcongr
          exact (Real.abs_sin_sub_sin_le _ _).trans hd
      _ = ((s0.r : ℝ) + (cdiv (U.r * 62832) 10000 : ℕ)) / 2 ^ P := by ring

end Ival.Ball
