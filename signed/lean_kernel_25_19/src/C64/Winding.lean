import C64.CertProp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Piecewise
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
# Winding numbers along parametrized curves

`LogChange g a b Δ`: `g` has a continuous logarithm on `[a, b]` whose total change is `Δ`; `HasWinding g n` is
`LogChange g 0 1 (2πi n)`.  This file proves:

* uniqueness of the change (`LogChange.unique`, by the intermediate value theorem);
* concatenation (`LogChange.trans`) and existence for nonvanishing continuous `g` (`exists_logChange`);
* `c · F²` winds an even number of times around `0` along a closed curve (`hasWinding_even_of_sq`);
* homotopy invariance (`hasWinding_homotopy`), by local constancy: along a short step of the homotopy the ratio of
  the two loops stays in the right half-plane, where the principal logarithm is continuous;
* the half-plane label formula (`HP`, `brl`, `LogChange.ofHP`, `LogChange.comb`): a curve cut into pieces that map
  into open half-planes winds `∑ jumps` times, where a jump is `+1` for a label change `3 → 0` and `-1` for `0 → 3`.
-/

open Set Complex Real Filter Topology

namespace C64

/-- `g` has a continuous logarithm on `[a, b]` whose total change is `Δ`. -/
def LogChange (g : ℝ → ℂ) (a b : ℝ) (Δ : ℂ) : Prop :=
  ∃ L : ℝ → ℂ, ContinuousOn L (Icc a b) ∧ (∀ s ∈ Icc a b, Complex.exp (L s) = g s) ∧ L b - L a = Δ

lemma hasWinding_iff (g : ℝ → ℂ) (n : ℤ) : HasWinding g n ↔ LogChange g 0 1 (2 * π * I * n) := Iff.rfl

/-! ### Uniqueness -/

/-- A continuous integer-valued function on an interval takes the same value at both ends. -/
lemma intValued_eq {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hint : ∀ x ∈ Icc a b, ∃ k : ℤ, f x = k) : f a = f b := by
  obtain ⟨ka, hka⟩ := hint a ⟨le_rfl, hab⟩
  obtain ⟨kb, hkb⟩ := hint b ⟨hab, le_rfl⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · rw [hka, hkb] at h
    have hk : ka < kb := by exact_mod_cast h
    have hk1 : (ka : ℝ) + 1 ≤ kb := by exact_mod_cast hk
    have hmem : (ka : ℝ) + 1 / 2 ∈ Icc (f a) (f b) := by rw [hka, hkb]; constructor <;> linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hf hmem
    obtain ⟨k, hk'⟩ := hint x hx
    rw [hk'] at hfx
    have h2 : ((2 * k : ℤ) : ℝ) = ((2 * ka + 1 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective h2
    omega
  · rw [hka, hkb] at h
    have hk : kb < ka := by exact_mod_cast h
    have hk1 : (kb : ℝ) + 1 ≤ ka := by exact_mod_cast hk
    have hmem : (kb : ℝ) + 1 / 2 ∈ Icc (f b) (f a) := by rw [hka, hkb]; constructor <;> linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hf hmem
    obtain ⟨k, hk'⟩ := hint x hx
    rw [hk'] at hfx
    have h2 : ((2 * k : ℤ) : ℝ) = ((2 * kb + 1 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective h2
    omega

lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The total change of a continuous logarithm does not depend on the logarithm. -/
theorem LogChange.unique {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) {Δ₁ Δ₂ : ℂ}
    (h₁ : LogChange g a b Δ₁) (h₂ : LogChange g a b Δ₂) : Δ₁ = Δ₂ := by
  obtain ⟨L₁, c₁, e₁, d₁⟩ := h₁
  obtain ⟨L₂, c₂, e₂, d₂⟩ := h₂
  have hD : ∀ s ∈ Icc a b, ∃ k : ℤ, L₁ s - L₂ s = k * (2 * π * I) := fun s hs => by
    rw [← Complex.exp_eq_one_iff, Complex.exp_sub, e₁ s hs, e₂ s hs, div_self]
    rw [← e₁ s hs]; exact Complex.exp_ne_zero _
  set f : ℝ → ℝ := fun s => (L₁ s - L₂ s).im / (2 * π)
  have hf : ContinuousOn f (Icc a b) :=
    (Complex.continuous_im.comp_continuousOn (c₁.sub c₂)).div_const _
  have hint : ∀ s ∈ Icc a b, ∃ k : ℤ, f s = k := fun s hs => by
    obtain ⟨k, hk⟩ := hD s hs
    refine ⟨k, ?_⟩
    simp only [f, hk]
    have : ((k : ℂ) * (2 * π * I)).im = k * (2 * π) := by simp
    rw [this]; field_simp
  have hconst := intValued_eq hab hf hint
  obtain ⟨ka, hka⟩ := hD a ⟨le_rfl, hab⟩
  obtain ⟨kb, hkb⟩ := hD b ⟨hab, le_rfl⟩
  have hfa : f a = ka := by
    simp only [f, hka]; have : ((ka : ℂ) * (2 * π * I)).im = ka * (2 * π) := by simp
    rw [this]; field_simp
  have hfb : f b = kb := by
    simp only [f, hkb]; have : ((kb : ℂ) * (2 * π * I)).im = kb * (2 * π) := by simp
    rw [this]; field_simp
  have hk : ka = kb := by
    have : (ka : ℝ) = kb := by rw [← hfa, ← hfb, hconst]
    exact_mod_cast this
  rw [← d₁, ← d₂]
  have : L₁ b - L₂ b = L₁ a - L₂ a := by rw [hka, hkb, hk]
  linear_combination this

theorem HasWinding.unique {g : ℝ → ℂ} {n m : ℤ} (hn : HasWinding g n) (hm : HasWinding g m) : n = m := by
  have := LogChange.unique zero_le_one hn hm
  have h2 : (2 * π * I : ℂ) * n = 2 * π * I * m := this
  have h3 : (n : ℂ) = m := mul_left_cancel₀ two_pi_I_ne_zero h2
  exact_mod_cast h3

/-! ### Concatenation and existence -/

/-- Logarithms on adjacent intervals glue (after a shift by a multiple of `2πi`). -/
theorem LogChange.trans {g : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {Δ₁ Δ₂ : ℂ}
    (h₁ : LogChange g a b Δ₁) (h₂ : LogChange g b c Δ₂) : LogChange g a c (Δ₁ + Δ₂) := by
  obtain ⟨L₁, c₁, e₁, d₁⟩ := h₁
  obtain ⟨L₂, c₂, e₂, d₂⟩ := h₂
  set k := L₁ b - L₂ b with hk
  have hek : Complex.exp k = 1 := by
    rw [hk, Complex.exp_sub, e₁ b ⟨hab, le_rfl⟩, e₂ b ⟨le_rfl, hbc⟩, div_self]
    rw [← e₂ b ⟨le_rfl, hbc⟩]; exact Complex.exp_ne_zero _
  refine ⟨fun s => if s ≤ b then L₁ s else L₂ s + k, ?_, ?_, ?_⟩
  · apply ContinuousOn.if
    · intro s ⟨_, hfr⟩
      have hs : s = b := by
        have : frontier {x : ℝ | x ≤ b} = {b} := frontier_Iic
        rw [this] at hfr; exact hfr
      subst hs; simp [hk]
    · refine c₁.mono ?_
      intro s ⟨hs, hcl⟩
      have : closure {x : ℝ | x ≤ b} = Iic b := closure_Iic b
      rw [this] at hcl
      exact ⟨hs.1, hcl⟩
    · refine (c₂.add continuousOn_const).mono ?_
      intro s ⟨hs, hcl⟩
      have : closure {x : ℝ | ¬x ≤ b} = Ici b := by
        have : {x : ℝ | ¬x ≤ b} = Ioi b := by ext x; simp
        rw [this, closure_Ioi]
      rw [this] at hcl
      exact ⟨hcl, hs.2⟩
  · intro s hs
    simp only
    split_ifs with h
    · exact e₁ s ⟨hs.1, h⟩
    · rw [Complex.exp_add, e₂ s ⟨(not_le.1 h).le, hs.2⟩, hek, mul_one]
  · simp only
    rcases eq_or_lt_of_le hbc with hbc' | hbc'
    · subst hbc'
      have : L₂ b - L₂ b = Δ₂ := d₂
      simp only [le_refl, ite_true, hab, sub_self] at this ⊢
      rw [← d₁, ← this]; ring
    · simp only [not_le.2 hbc', hab, ite_true, ite_false]
      rw [hk, ← d₁, ← d₂]; ring

lemma LogChange.refl {g : ℝ → ℂ} {a : ℝ} (ha : g a ≠ 0) : LogChange g a a 0 :=
  ⟨fun _ => Complex.log (g a), continuousOn_const, fun s hs => by
    rw [show s = a from le_antisymm hs.2 hs.1, Complex.exp_log ha], sub_self _⟩

/-- A curve that stays within distance `‖g a‖` of `g a` has a logarithm (via the principal branch of the ratio). -/
theorem LogChange.of_near {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hnear : ∀ s ∈ Icc a b, ‖g s - g a‖ < ‖g a‖) : LogChange g a b (Complex.log (g b / g a)) := by
  have ha : g a ≠ 0 := by
    intro h; have := hnear a ⟨le_rfl, hab⟩; simp [h] at this
  have hre : ∀ s ∈ Icc a b, 0 < (g s / g a).re := by
    intro s hs
    have h1 : ‖g s / g a - 1‖ < 1 := by
      rw [show g s / g a - 1 = (g s - g a) / g a by field_simp, norm_div,
        div_lt_one (norm_pos_iff.2 ha)]
      exact hnear s hs
    have h2 : |(g s / g a - 1).re| ≤ ‖g s / g a - 1‖ := Complex.abs_re_le_norm _
    have h3 : (g s / g a - 1).re = (g s / g a).re - 1 := by simp
    rw [h3] at h2
    linarith [(abs_lt.1 (lt_of_le_of_lt h2 h1)).1]
  refine ⟨fun s => Complex.log (g a) + Complex.log (g s / g a), ?_, ?_, ?_⟩
  · refine continuousOn_const.add (ContinuousOn.clog (hg.div_const _) ?_)
    intro s hs; exact Complex.mem_slitPlane_iff.2 (Or.inl (hre s hs))
  · intro s hs
    have hs0 : g s / g a ≠ 0 := by
      intro h; have := hre s hs; rw [h] at this; simp at this
    rw [Complex.exp_add, Complex.exp_log ha, Complex.exp_log hs0]; field_simp
  · simp [div_self ha]

/-- Every continuous nonvanishing curve on `[a, b]` has a continuous logarithm. -/
theorem exists_logChange {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (h0 : ∀ s ∈ Icc a b, g s ≠ 0) : ∃ Δ, LogChange g a b Δ := by
  -- a positive lower bound for ‖g‖
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_isMinOn
    (nonempty_Icc.2 hab) (continuous_norm.comp_continuousOn hg)
  set m := ‖g s₀‖ with hm
  have hmpos : 0 < m := norm_pos_iff.2 (h0 s₀ hs₀)
  have hmle : ∀ s ∈ Icc a b, m ≤ ‖g s‖ := fun s hs => hmin hs
  -- uniform continuity
  have huc := (isCompact_Icc : IsCompact (Icc a b)).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc m hmpos
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg (by linarith) hδ.le) hN
  set x : ℕ → ℝ := fun k => a + k * ((b - a) / N) with hx
  have hstep : (b - a) / N < δ := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hδ] at hN; linarith
  have hxmono : ∀ k, x k ≤ x (k + 1) := fun k => by
    simp only [hx]; push_cast
    have : 0 ≤ (b - a) / N := div_nonneg (by linarith) hNpos.le
    nlinarith
  have hxmem : ∀ k ≤ N, x k ∈ Icc a b := fun k hk => by
    simp only [hx]
    have h1 : 0 ≤ (b - a) / N := div_nonneg (by linarith) hNpos.le
    have h2 : (k : ℝ) ≤ N := by exact_mod_cast hk
    constructor
    · nlinarith
    · have : (k : ℝ) * ((b - a) / N) ≤ N * ((b - a) / N) := mul_le_mul_of_nonneg_right h2 h1
      rw [mul_div_cancel₀ _ hNpos.ne'] at this; linarith
  have hk : ∀ k ≤ N, ∃ Δ, LogChange g a (x k) Δ := by
    intro k
    induction k with
    | zero => intro _; refine ⟨0, ?_⟩; simp only [hx, Nat.cast_zero, zero_mul, add_zero]
              exact LogChange.refl (h0 a ⟨le_rfl, hab⟩)
    | succ k ih =>
      intro hk1
      obtain ⟨Δ, hΔ⟩ := ih (Nat.le_of_succ_le hk1)
      have hxk := hxmem k (Nat.le_of_succ_le hk1)
      have hxk1 := hxmem (k + 1) hk1
      have hsub : Icc (x k) (x (k + 1)) ⊆ Icc a b := Icc_subset_Icc hxk.1 hxk1.2
      have hpiece := LogChange.of_near (hxmono k) (hg.mono hsub) (fun s hs => by
        have hsm := hsub hs
        have hdist : dist s (x k) < δ := by
          rw [Real.dist_eq, abs_lt]
          have : x (k + 1) - x k = (b - a) / N := by simp only [hx]; push_cast; ring
          constructor <;> linarith [hs.1, hs.2]
        have := hδc s hsm (x k) hxk hdist
        rw [dist_eq_norm] at this
        exact lt_of_lt_of_le this (hmle (x k) hxk))
      exact ⟨Δ + _, LogChange.trans hxk.1 (hxmono k) hΔ hpiece⟩
  obtain ⟨Δ, hΔ⟩ := hk N le_rfl
  have hxN : x N = b := by simp only [hx]; field_simp; ring
  rw [hxN] at hΔ
  exact ⟨Δ, hΔ⟩

/-! ### Squares wind an even number of times -/

/-- If `g = c F²` along a closed curve with `F` continuous and nonvanishing, every winding number of `g` is even. -/
theorem hasWinding_even_of_sq {F g : ℝ → ℂ} (hF : ContinuousOn F (Icc 0 1)) (hF0 : ∀ s ∈ Icc (0 : ℝ) 1, F s ≠ 0)
    (hper : F 0 = F 1) {c : ℂ} (hc : c ≠ 0) (hg : ∀ s ∈ Icc (0 : ℝ) 1, g s = c * F s ^ 2) {n : ℤ}
    (hn : HasWinding g n) : Even n := by
  obtain ⟨Δ, LF, cF, eF, dF⟩ := exists_logChange zero_le_one hF hF0
  -- Δ = 2πi m
  have hexp : Complex.exp Δ = 1 := by
    rw [← dF, Complex.exp_sub, eF 1 ⟨zero_le_one, le_rfl⟩, eF 0 ⟨le_rfl, zero_le_one⟩, hper, div_self]
    exact hF0 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
  -- a logarithm of g with change 2Δ
  have hlog : HasWinding g (2 * m) := by
    refine ⟨fun s => Complex.log c + 2 * LF s, continuousOn_const.add (continuousOn_const.mul cF), ?_, ?_⟩
    · intro s hs
      rw [Complex.exp_add, Complex.exp_log hc, hg s hs, two_mul, Complex.exp_add, eF s hs]; ring
    · have : LF 1 - LF 0 = Δ := dF
      push_cast
      linear_combination 2 * this + 2 * hm
  rw [hn.unique hlog]; exact even_two_mul m

/-! ### Homotopy invariance -/

/-- Along a homotopy of closed curves that avoids `0`, the winding number is constant. -/
theorem hasWinding_homotopy {H : ℝ → ℝ → ℂ}
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1))
    (hne : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H θ s ≠ 0)
    (hper : ∀ θ ∈ Icc (0 : ℝ) 1, H θ 0 = H θ 1) {n : ℤ} (h0 : HasWinding (H 0) n) : HasWinding (H 1) n := by
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hH)
  set m := ‖H p₀.1 p₀.2‖
  have hmpos : 0 < m := norm_pos_iff.2 (hne _ hp₀.1 _ hp₀.2)
  have hmle : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, m ≤ ‖H θ s‖ := fun θ hθ s hs =>
    hmin (show (θ, s) ∈ K from ⟨hθ, hs⟩)
  have huc := hKc.uniformContinuousOn_of_continuous hH
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc m hmpos
  -- one short step of the homotopy
  have step : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ θ' ∈ Icc (0 : ℝ) 1, |θ' - θ| < δ →
      HasWinding (H θ) n → HasWinding (H θ') n := by
    intro θ hθ θ' hθ' hd ⟨L, cL, eL, dL⟩
    have hre : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (H θ' s / H θ s).re := by
      intro s hs
      have hdist : dist (θ', s) (θ, s) < δ := by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero, max_eq_left (abs_nonneg _)]
        exact hd
      have h1 := hδc (θ', s) ⟨hθ', hs⟩ (θ, s) ⟨hθ, hs⟩ hdist
      rw [dist_eq_norm] at h1
      have hHs := hne θ hθ s hs
      have h2 : ‖H θ' s / H θ s - 1‖ < 1 := by
        rw [show H θ' s / H θ s - 1 = (H θ' s - H θ s) / H θ s by field_simp, norm_div,
          div_lt_one (norm_pos_iff.2 hHs)]
        exact lt_of_lt_of_le h1 (hmle θ hθ s hs)
      have h3 : |(H θ' s / H θ s - 1).re| ≤ ‖H θ' s / H θ s - 1‖ := Complex.abs_re_le_norm _
      have h4 : (H θ' s / H θ s - 1).re = (H θ' s / H θ s).re - 1 := by simp
      rw [h4] at h3
      linarith [(abs_lt.1 (lt_of_le_of_lt h3 h2)).1]
    have hcont : ContinuousOn (fun s => H θ' s / H θ s) (Icc 0 1) := by
      have c1 : ContinuousOn (fun s => H θ' s) (Icc 0 1) :=
        hH.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hθ', hs⟩)
      have c2 : ContinuousOn (fun s => H θ s) (Icc 0 1) :=
        hH.comp (continuousOn_const.prodMk continuousOn_id) (fun s hs => ⟨hθ, hs⟩)
      exact c1.div c2 (fun s hs => hne θ hθ s hs)
    refine ⟨fun s => L s + Complex.log (H θ' s / H θ s),
      cL.add (ContinuousOn.clog hcont (fun s hs => Complex.mem_slitPlane_iff.2 (Or.inl (hre s hs)))), ?_, ?_⟩
    · intro s hs
      have hq : H θ' s / H θ s ≠ 0 := by
        intro h; have := hre s hs; rw [h] at this; simp at this
      rw [Complex.exp_add, eL s hs, Complex.exp_log hq]
      field_simp [hne θ hθ s hs]
    · have hp0 := hper θ hθ
      have hp1 := hper θ' hθ'
      simp only
      rw [← hp0, ← hp1]
      linear_combination dL
  -- chain the steps from θ = 0 to θ = 1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < (N : ℝ) := lt_of_le_of_lt (div_nonneg zero_le_one hδ.le) hN
  have hstep : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hδ] at hN; linarith
  have hk : ∀ k ≤ N, HasWinding (H (k / N)) n := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk1
      have hk' : k ≤ N := Nat.le_of_succ_le hk1
      have hmemk : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity,
        (div_le_one hNpos).2 (by exact_mod_cast hk')⟩
      have hmemk1 : ((k + 1 : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity,
        (div_le_one hNpos).2 (by exact_mod_cast hk1)⟩
      refine step _ hmemk _ hmemk1 ?_ (ih hk')
      rw [show ((k + 1 : ℕ) : ℝ) / N - k / N = 1 / N by push_cast; ring, abs_of_pos (by positivity)]
      exact hstep
  have := hk N le_rfl
  rwa [div_self hNpos.ne'] at this

/-! ### Half-plane labels -/

/-- The open half-plane with label `h` (mod 4): `Re (w (-i)^h) > 0`; for `h = 0, 1, 2, 3` these are `Re w > 0`,
`Im w > 0`, `Re w < 0`, `Im w < 0`. -/
def HP (h : ℕ) (w : ℂ) : Prop := 0 < (w * (-I) ^ h).re

/-- The branch of the logarithm on `HP h`: `log (w (-i)^h) + i h π/2`. -/
noncomputable def brl (h : ℕ) (w : ℂ) : ℂ := Complex.log (w * (-I) ^ h) + I * (h * (π / 2))

lemma HP.ne_zero {h : ℕ} {w : ℂ} (hw : HP h w) : w ≠ 0 := by
  intro h0; simp [HP, h0] at hw

lemma exp_I_mul_half_pi (h : ℕ) : Complex.exp (I * (h * (π / 2))) = I ^ h := by
  rw [show I * ((h : ℂ) * (π / 2)) = (h : ℂ) * (π / 2 * I) by ring, Complex.exp_nat_mul,
    Complex.exp_pi_div_two_mul_I]

lemma exp_brl {h : ℕ} {w : ℂ} (hw : HP h w) : Complex.exp (brl h w) = w := by
  have hne : w * (-I) ^ h ≠ 0 := by
    intro h0; simp [HP, h0] at hw
  rw [brl, Complex.exp_add, Complex.exp_log hne, exp_I_mul_half_pi, mul_assoc, ← mul_pow]
  simp

lemma brl_im {h : ℕ} {w : ℂ} (hw : HP h w) :
    h * (π / 2) - π / 2 < (brl h w).im ∧ (brl h w).im < h * (π / 2) + π / 2 := by
  have harg : |(w * (-I) ^ h).arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have him : (brl h w).im = (w * (-I) ^ h).arg + h * (π / 2) := by
    simp [brl, Complex.log_im]
  rw [him]
  constructor <;> linarith [(abs_lt.1 harg).1, (abs_lt.1 harg).2]

/-- Jump between branches: `+1` for `3 → 0`, `-1` for `0 → 3`, `0` otherwise. -/
def jmp (h h' : ℕ) : ℤ := if h = 3 ∧ h' = 0 then 1 else if h = 0 ∧ h' = 3 then -1 else 0

/-- At a point of two half-planes the branches differ by `2πi · jmp`. -/
theorem brl_sub {h h' : ℕ} (hh : h < 4) (hh' : h' < 4) {w : ℂ} (hw : HP h w) (hw' : HP h' w) :
    brl h w - brl h' w = 2 * π * I * jmp h h' := by
  have hexp : Complex.exp (brl h w - brl h' w) = 1 := by
    rw [Complex.exp_sub, exp_brl hw, exp_brl hw', div_self hw.ne_zero]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
  have b1 := brl_im hw
  have b2 := brl_im hw'
  have him : (brl h w - brl h' w).im = k * (2 * π) := by rw [hk]; simp
  rw [Complex.sub_im] at him
  have hpi := Real.pi_pos
  -- (h - h') π/2 - π < 2πk < (h - h') π/2 + π
  have hlo : ((h : ℝ) - h') * (π / 2) - π < k * (2 * π) := by rw [← him]; nlinarith
  have hhi : k * (2 * π) < ((h : ℝ) - h') * (π / 2) + π := by rw [← him]; nlinarith
  have hlo' : ((h : ℝ) - h') - 2 < 4 * k := by
    have : (((h : ℝ) - h') - 2) * (π / 2) < (4 * k) * (π / 2) := by nlinarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hhi' : 4 * (k : ℝ) < ((h : ℝ) - h') + 2 := by
    have : (4 * k) * (π / 2) < (((h : ℝ) - h') + 2) * (π / 2) := by nlinarith
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hlo'' : (h : ℤ) - h' - 2 < 4 * k := by exact_mod_cast hlo'
  have hhi'' : 4 * k < (h : ℤ) - h' + 2 := by exact_mod_cast hhi'
  rw [hk]
  have hj : jmp h h' = k := by
    unfold jmp
    interval_cases h <;> interval_cases h' <;> simp at hlo'' hhi'' ⊢ <;> omega
  rw [hj]; ring

/-- A labelled logarithm on `[a, b]`: first label `hf` at `a`, last label `hl` at `b`, internal jumps `W`. -/
def LabLC (g : ℝ → ℂ) (a b : ℝ) (hf hl : ℕ) (W : ℤ) : Prop :=
  hf < 4 ∧ hl < 4 ∧ HP hf (g a) ∧ HP hl (g b) ∧
    LogChange g a b (brl hl (g b) - brl hf (g a) + 2 * π * I * W)

/-- A piece that maps into one half-plane. -/
theorem LabLC.piece {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) {h : ℕ} (hh : h < 4)
    (hp : ∀ s ∈ Icc a b, HP h (g s)) : LabLC g a b h h 0 := by
  refine ⟨hh, hh, hp a ⟨le_rfl, hab⟩, hp b ⟨hab, le_rfl⟩, fun s => brl h (g s), ?_, ?_, ?_⟩
  · refine (ContinuousOn.clog (hg.mul continuousOn_const) ?_).add continuousOn_const
    intro s hs; exact Complex.mem_slitPlane_iff.2 (Or.inl (hp s hs))
  · intro s hs; exact exp_brl (hp s hs)
  · simp

/-- Concatenation of labelled logarithms. -/
theorem LabLC.comb {g : ℝ → ℂ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) {hf₁ hl₁ hf₂ hl₂ : ℕ} {W₁ W₂ : ℤ}
    (h₁ : LabLC g a m hf₁ hl₁ W₁) (h₂ : LabLC g m b hf₂ hl₂ W₂) :
    LabLC g a b hf₁ hl₂ (W₁ + W₂ + jmp hl₁ hf₂) := by
  obtain ⟨f1, l1, pf1, pl1, c1⟩ := h₁
  obtain ⟨f2, l2, pf2, pl2, c2⟩ := h₂
  refine ⟨f1, l2, pf1, pl2, ?_⟩
  have := LogChange.trans ham hmb c1 c2
  have hj := brl_sub l1 f2 pl1 pf2
  convert this using 1
  push_cast
  linear_combination -hj

/-- A closed labelled curve has winding number `W + jmp hl hf`. -/
theorem LabLC.close {g : ℝ → ℂ} {hf hl : ℕ} {W : ℤ} (h : LabLC g 0 1 hf hl W) (hper : g 0 = g 1) :
    HasWinding g (W + jmp hl hf) := by
  obtain ⟨f1, l1, pf, pl, c⟩ := h
  rw [hper] at pf
  have hj := brl_sub l1 f1 pl pf
  rw [hasWinding_iff]
  convert c using 1
  rw [← hper] at hj ⊢
  push_cast
  linear_combination -hj

end C64
