import C64.Reduction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of `S` and `K_t` and the bounds used by the checker

* `S1 z = ∫_{-1/2}^{1/2} (-2πit) K_t(z) dt` and `S2 z = ∫ (-2πit)² K_t(z) dt` are `S'` and `S''`;
* `norm_S2_le`: `|S''(w)| ≤ (π²/3) e^{π |Im w|}`; `norm_S1_le_disc`: local bound for `|S'|` on a disc;
* `S1_eq`: `S'(z) = (π z cos(π z) - sin(π z)) / (π z²)` for `z ≠ 0` (the formula the checker evaluates);
* `norm_sub_Kt_le`: `|K_t(z) - K_t(z')| ≤ π e^{π Y} |z - z'|` on a convex set where `|Im| ≤ Y`, `|t| ≤ 1/2`.
-/

open MeasureTheory Set Complex Real Filter Topology
open scoped Interval

namespace C64

/-- `S'`. -/
noncomputable def S1 (z : ℂ) : ℂ := ∫ t in (-1/2 : ℝ)..(1/2), (-2 * π * I * t) * Kt t z

/-- `S''`. -/
noncomputable def S2 (z : ℂ) : ℂ := ∫ t in (-1/2 : ℝ)..(1/2), (-2 * π * I * t) ^ 2 * Kt t z

lemma hasDerivAt_Kt (t : ℝ) (z : ℂ) : HasDerivAt (Kt t) ((-2 * π * I * t) * Kt t z) z := by
  unfold Kt
  have := ((hasDerivAt_id z).const_mul (-2 * π * I * t)).cexp
  convert this using 1 <;> [ext w; skip] <;> simp [mul_comm, mul_left_comm]

lemma norm_Kt_le' {t : ℝ} (ht : t ∈ Ι (-1/2 : ℝ) (1/2)) (z : ℂ) : ‖Kt t z‖ ≤ Real.exp (π * |z.im|) := by
  rw [uIoc_of_le (by norm_num)] at ht
  exact norm_Kt_le ⟨ht.1.le, ht.2⟩ z

lemma abs_t_le {t : ℝ} (ht : t ∈ Ι (-1/2 : ℝ) (1/2)) : |t| ≤ 1/2 := by
  rw [uIoc_of_le (by norm_num)] at ht
  exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩

lemma norm_im_le_of_dist {z z₀ : ℂ} (h : dist z z₀ < 1) : |z.im| ≤ |z₀.im| + 1 := by
  have h1 : |z.im - z₀.im| ≤ dist z z₀ := by
    rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm _).trans_eq' (by simp)
  have := abs_sub_abs_le_abs_sub z.im z₀.im
  linarith

/-- Differentiation under the integral sign for `∫ g(t) K_t(z) dt`, `g` continuous with `|g| ≤ G` on `[-1/2,1/2]`. -/
lemma hasDerivAt_integral_mul_Kt {g : ℝ → ℂ} (hg : Continuous g) {G : ℝ}
    (hG : ∀ t ∈ Ι (-1/2 : ℝ) (1/2), ‖g t‖ ≤ G) (z₀ : ℂ) :
    HasDerivAt (fun z => ∫ t in (-1/2 : ℝ)..(1/2), g t * Kt t z)
      (∫ t in (-1/2 : ℝ)..(1/2), g t * ((-2 * π * I * t) * Kt t z₀)) z₀ := by
  have hcont : ∀ z, Continuous (fun t : ℝ => g t * Kt t z) := fun z => hg.mul (continuous_Kt_t z)
  have hcont' : ∀ z, Continuous (fun t : ℝ => g t * ((-2 * π * I * t) * Kt t z)) := fun z =>
    hg.mul ((continuous_const.mul Complex.continuous_ofReal).mul (continuous_Kt_t z))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => g t * Kt t z) (F' := fun z t => g t * ((-2 * π * I * t) * Kt t z))
    (bound := fun _ => G * (π * Real.exp (π * (|z₀.im| + 1))))
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall (fun z => (hcont z).aestronglyMeasurable))
    ((hcont z₀).intervalIntegrable _ _) (hcont' z₀).aestronglyMeasurable ?_ intervalIntegrable_const ?_).2
  · refine Eventually.of_forall (fun t ht z hz => ?_)
    have hG0 := hG t ht
    rw [norm_mul, norm_mul]
    have h1 : ‖(-2 * π * I * t : ℂ)‖ ≤ π := by
      have : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [this]; nlinarith [abs_t_le ht, Real.pi_pos]
    have h2 : ‖Kt t z‖ ≤ Real.exp (π * (|z₀.im| + 1)) :=
      (norm_Kt_le' ht z).trans (Real.exp_le_exp.2 (by nlinarith [norm_im_le_of_dist hz, Real.pi_pos]))
    have hG0' : 0 ≤ ‖g t‖ := norm_nonneg _
    exact mul_le_mul hG0 (mul_le_mul h1 h2 (norm_nonneg _) Real.pi_pos.le) (by positivity) (hG0'.trans hG0)
  · refine Eventually.of_forall (fun t _ z _ => ?_)
    exact (hasDerivAt_Kt t z).const_mul (g t)

lemma hasDerivAt_S (z : ℂ) : HasDerivAt S (S1 z) z := by
  have h := hasDerivAt_integral_mul_Kt (g := fun _ => (1 : ℂ)) continuous_const (G := 1)
    (fun t _ => by simp) z
  have e1 : (fun z => ∫ t in (-1/2 : ℝ)..(1/2), (1 : ℂ) * Kt t z) = S := by
    funext w; rw [S_eq_integral]; simp
  rw [e1] at h
  simpa [S1] using h

lemma hasDerivAt_S1 (z : ℂ) : HasDerivAt S1 (S2 z) z := by
  have h := hasDerivAt_integral_mul_Kt (g := fun t : ℝ => (-2 * π * I * t : ℂ))
    (continuous_const.mul Complex.continuous_ofReal) (G := π) (fun t ht => by
      have : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [this]; nlinarith [abs_t_le ht, Real.pi_pos]) z
  have e2 : (fun t : ℝ => (-2 * π * I * t : ℂ) * ((-2 * π * I * t) * Kt t z)) =
      fun t : ℝ => (-2 * π * I * t : ℂ) ^ 2 * Kt t z := by funext t; ring
  rw [e2] at h
  exact h

/-- `|S''(w)| ≤ (π²/3) e^{π |Im w|}`. -/
theorem norm_S2_le (w : ℂ) : ‖S2 w‖ ≤ π ^ 2 / 3 * Real.exp (π * |w.im|) := by
  have h : ‖S2 w‖ ≤ ∫ t in (-1/2 : ℝ)..(1/2), (4 * π ^ 2 * Real.exp (π * |w.im|)) * t ^ 2 := by
    rw [S2]
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ ?_
    · refine Eventually.of_forall (fun t ht => ?_)
      rw [norm_mul, norm_pow]
      have h1 : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
      rw [h1]
      have h2 : ‖Kt t w‖ ≤ Real.exp (π * |w.im|) := by
        have : t ∈ Ι (-1/2 : ℝ) (1/2) := by rw [uIoc_of_le (by norm_num)]; exact ht
        exact norm_Kt_le' this w
      calc (2 * π * |t|) ^ 2 * ‖Kt t w‖ ≤ (2 * π * |t|) ^ 2 * Real.exp (π * |w.im|) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 4 * π ^ 2 * Real.exp (π * |w.im|) * t ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
    · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, integral_pow] at h
  norm_num at h
  linarith

/-- The checker's formula: `S'(z) = (π z cos(π z) - sin(π z)) / (π z²)` for `z ≠ 0`. -/
theorem S1_eq {z : ℂ} (hz : z ≠ 0) :
    S1 z = (π * z * Complex.cos (π * z) - Complex.sin (π * z)) / (π * z ^ 2) := by
  have hpz : (π * z : ℂ) ≠ 0 := by simp [hz, Real.pi_ne_zero]
  -- S agrees with sin(πz)/(πz) near z
  have heq : S =ᶠ[𝓝 z] fun w => Complex.sin (π * w) / (π * w) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp [S, hw]
  have hd : HasDerivAt (fun w => Complex.sin (π * w) / (π * w))
      ((π * Complex.cos (π * z) * (π * z) - Complex.sin (π * z) * π) / (π * z) ^ 2) z := by
    have h1 : HasDerivAt (fun w : ℂ => Complex.sin (π * w)) (Complex.cos (π * z) * π) z := by
      have := (Complex.hasDerivAt_sin (π * z)).comp z ((hasDerivAt_id z).const_mul (π : ℂ))
      simp only [Function.comp_def, id, mul_one] at this
      exact this
    have h2 : HasDerivAt (fun w : ℂ => (π : ℂ) * w) π z := by
      simpa using (hasDerivAt_id z).const_mul (π : ℂ)
    have := h1.div h2 hpz
    convert this using 1; ring
  have := (hasDerivAt_S z).congr_of_eventuallyEq heq.symm
  rw [(hasDerivAt_S z).unique (hd.congr_of_eventuallyEq heq)]
  field_simp

/-- `|K_t(z) - K_t(z')| ≤ π e^{π Y} |z - z'|` for `|t| ≤ 1/2` on a convex set where `|Im| ≤ Y`. -/
theorem norm_sub_Kt_le {t : ℝ} (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) {U : Set ℂ} (hU : Convex ℝ U) {Y : ℝ}
    (hY : ∀ ζ ∈ U, |ζ.im| ≤ Y) {z z' : ℂ} (hz : z ∈ U) (hz' : z' ∈ U) :
    ‖Kt t z - Kt t z'‖ ≤ π * Real.exp (π * Y) * ‖z - z'‖ := by
  refine hU.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Kt t)
    (fun ζ _ => (hasDerivAt_Kt t ζ).hasDerivWithinAt) (fun ζ hζ => ?_) hz' hz
  rw [norm_mul]
  have h1 : ‖(-2 * π * I * t : ℂ)‖ ≤ π := by
    have : ‖(-2 * π * I * t : ℂ)‖ = 2 * π * |t| := by simp [Real.pi_pos.le]
    rw [this]; nlinarith [abs_le.2 ⟨by linarith [ht.1], ht.2⟩, Real.pi_pos]
  exact mul_le_mul h1 ((norm_Kt_le ht ζ).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left (hY ζ hζ) Real.pi_pos.le))) (norm_nonneg _) Real.pi_pos.le

/-- `|S(z) - S(z')| ≤ L |z - z'|` on a convex set where `|S'| ≤ L`. -/
theorem norm_sub_S_le {U : Set ℂ} (hU : Convex ℝ U) {L : ℝ} (hL : ∀ ζ ∈ U, ‖S1 ζ‖ ≤ L) {z z' : ℂ}
    (hz : z ∈ U) (hz' : z' ∈ U) : ‖S z - S z'‖ ≤ L * ‖z - z'‖ :=
  hU.norm_image_sub_le_of_norm_hasDerivWithin_le (fun ζ _ => (hasDerivAt_S ζ).hasDerivWithinAt) hL hz' hz

/-- `|S'(ζ)| ≤ |S'(z₀)| + ρ (π²/3) e^{π Y}` on the disc `D(z₀, ρ)` when `|Im| ≤ Y` there. -/
theorem norm_S1_le_disc {z₀ ζ : ℂ} {ρ Y : ℝ} (hζ : ζ ∈ Metric.closedBall z₀ ρ)
    (hY : ∀ w ∈ Metric.closedBall z₀ ρ, |w.im| ≤ Y) :
    ‖S1 ζ‖ ≤ ‖S1 z₀‖ + ρ * (π ^ 2 / 3 * Real.exp (π * Y)) := by
  have h := (convex_closedBall z₀ ρ).norm_image_sub_le_of_norm_hasDerivWithin_le (f := S1) (f' := S2)
    (C := π ^ 2 / 3 * Real.exp (π * Y)) (fun w _ => (hasDerivAt_S1 w).hasDerivWithinAt)
    (fun w hw => (norm_S2_le w).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hY w hw) Real.pi_pos.le)) (by positivity)))
    (Metric.mem_closedBall_self (le_trans dist_nonneg hζ)) hζ
  have hd : ‖ζ - z₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact hζ
  have := norm_sub_norm_le (S1 ζ) (S1 z₀)
  have hC : 0 ≤ π ^ 2 / 3 * Real.exp (π * Y) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hd hC]

end C64
