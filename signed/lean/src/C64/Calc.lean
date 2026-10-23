import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Second-order Taylor bounds (copied from the sign-uncertainty project, where they are proved)

`taylor2_lower`: if `|f''| ≤ M` on `[y₀ - e, y₀ + e]`, then `f y ≥ f y₀ - |f'(y₀)| e - M e²/2` there;
`taylor2_upper` is the same for `-f`.
-/

open Real

namespace C64

/-- Second-order lower bound. -/
theorem taylor2_lower {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) {y₀ e M : ℝ} (he : 0 ≤ e)
    (hM : ∀ x ∈ Set.Icc (y₀ - e) (y₀ + e), |f2 x| ≤ M) :
    ∀ y ∈ Set.Icc (y₀ - e) (y₀ + e), f y₀ - |f1 y₀| * e - M * e ^ 2 / 2 ≤ f y := by
  intro y hy
  set h : ℝ → ℝ := fun x => f x - f y₀ - f1 y₀ * (x - y₀) + M * (x - y₀) ^ 2 / 2 with hh
  set h1 : ℝ → ℝ := fun x => f1 x - f1 y₀ + M * (x - y₀) with hh1
  have hd : ∀ x, HasDerivAt h (h1 x) x := by
    intro x
    have := ((((hf x).sub_const (f y₀)).sub (((hasDerivAt_id x).sub_const y₀).const_mul (f1 y₀))).add
      ((((hasDerivAt_id x).sub_const y₀).pow 2).const_mul M |>.div_const 2))
    refine this.congr_deriv ?_
    simp [hh1]; ring
  have hd1 : ∀ x, HasDerivAt h1 (f2 x + M) x := by
    intro x
    have := (((hf1 x).sub_const (f1 y₀)).add (((hasDerivAt_id x).sub_const y₀).const_mul M))
    refine this.congr_deriv ?_
    simp
  set D := Set.Icc (y₀ - e) (y₀ + e)
  have hconv : Convex ℝ D := convex_Icc _ _
  have hmono1 : MonotoneOn h1 D := by
    apply monotoneOn_of_deriv_nonneg hconv
    · exact fun x _ => (hd1 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd1 x).deriv]
      have := hM x (interior_subset hx)
      linarith [neg_abs_le (f2 x)]
  have h10 : h1 y₀ = 0 := by simp [hh1]
  have hy0 : y₀ ∈ D := ⟨by linarith, by linarith⟩
  have hnn : 0 ≤ h y := by
    rcases le_total y₀ y with hle | hle
    · -- monotone on [y₀, y]
      have hsub : Set.Icc y₀ y ⊆ D := fun x hx => ⟨by linarith [hx.1, hy0.1], by linarith [hx.2, hy.2]⟩
      have hm : MonotoneOn h (Set.Icc y₀ y) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hd x).deriv, ← h10]
          exact hmono1 hy0 (hsub ⟨hx.1.le, hx.2.le⟩) hx.1.le
      have := hm ⟨le_refl _, hle⟩ ⟨hle, le_refl _⟩ hle
      simpa [hh] using this
    · -- antitone on [y, y₀]
      have hsub : Set.Icc y y₀ ⊆ D := fun x hx => ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy0.2]⟩
      have hm : AntitoneOn h (Set.Icc y y₀) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun x _ => (hd x).continuousAt.continuousWithinAt
        · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hd x).deriv, ← h10]
          exact hmono1 (hsub ⟨hx.1.le, hx.2.le⟩) hy0 hx.2.le
      have := hm ⟨le_refl _, hle⟩ ⟨hle, le_refl _⟩ hle
      simpa [hh] using this
  simp only [hh] at hnn
  have habs : |y - y₀| ≤ e := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h1' : f1 y₀ * (y - y₀) ≥ -(|f1 y₀| * e) := by
    have := abs_mul (f1 y₀) (y - y₀)
    have h3 : |f1 y₀ * (y - y₀)| ≤ |f1 y₀| * e := by
      rw [this]; exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    linarith [neg_abs_le (f1 y₀ * (y - y₀))]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y₀ hy0)
  have h2' : M * (y - y₀) ^ 2 / 2 ≤ M * e ^ 2 / 2 := by
    have : (y - y₀) ^ 2 ≤ e ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have := mul_le_mul_of_nonneg_left this hM0
    linarith
  linarith

/-- One-sided second-order lower bound with the signed first derivative: if `|f''| ≤ M` on `[y₀, y₀ + e]`,
then `f y ≥ f y₀ + f'(y₀) (y - y₀) - M (y - y₀)²/2` there. -/
theorem taylor2_lower_right {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) {y₀ e M : ℝ}
    (hM : ∀ x ∈ Set.Icc y₀ (y₀ + e), |f2 x| ≤ M) :
    ∀ y ∈ Set.Icc y₀ (y₀ + e), f y₀ + f1 y₀ * (y - y₀) - M * (y - y₀) ^ 2 / 2 ≤ f y := by
  intro y hy
  set h : ℝ → ℝ := fun x => f x - f y₀ - f1 y₀ * (x - y₀) + M * (x - y₀) ^ 2 / 2 with hh
  set h1 : ℝ → ℝ := fun x => f1 x - f1 y₀ + M * (x - y₀) with hh1
  have hd : ∀ x, HasDerivAt h (h1 x) x := by
    intro x
    have := ((((hf x).sub_const (f y₀)).sub (((hasDerivAt_id x).sub_const y₀).const_mul (f1 y₀))).add
      ((((hasDerivAt_id x).sub_const y₀).pow 2).const_mul M |>.div_const 2))
    refine this.congr_deriv ?_
    simp [hh1]; ring
  have hd1 : ∀ x, HasDerivAt h1 (f2 x + M) x := by
    intro x
    have := (((hf1 x).sub_const (f1 y₀)).add (((hasDerivAt_id x).sub_const y₀).const_mul M))
    refine this.congr_deriv ?_
    simp
  set D := Set.Icc y₀ (y₀ + e)
  have hmono1 : MonotoneOn h1 D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd1 x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd1 x).deriv]
      have := hM x (interior_subset hx)
      linarith [neg_abs_le (f2 x)]
  have h10 : h1 y₀ = 0 := by simp [hh1]
  have hy0 : y₀ ∈ D := ⟨le_refl _, le_trans hy.1 hy.2⟩
  have hm : MonotoneOn h D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv, ← h10]
      exact hmono1 hy0 ⟨hx.1.le, hx.2.le⟩ hx.1.le
  have := hm hy0 hy hy.1
  simp only [hh] at this
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at this
  linarith

/-- Second-order upper bound. -/
theorem taylor2_upper {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) {y₀ e M : ℝ} (he : 0 ≤ e)
    (hM : ∀ x ∈ Set.Icc (y₀ - e) (y₀ + e), |f2 x| ≤ M) :
    ∀ y ∈ Set.Icc (y₀ - e) (y₀ + e), f y ≤ f y₀ + |f1 y₀| * e + M * e ^ 2 / 2 := by
  intro y hy
  have := taylor2_lower (f := fun x => -f x) (f1 := fun x => -f1 x) (f2 := fun x => -f2 x)
    (fun x => (hf x).neg) (fun x => (hf1 x).neg) he (fun x hx => by simpa using hM x hx) y hy
  simp only [abs_neg] at this
  linarith

end C64
