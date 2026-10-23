import Autocorr.C30.Main
import Autocorr.RealForm

/-! Further forms of the bound `C₁ ≥ 33/25` proved in `Autocorr.C30.Main`. -/

open MeasureTheory ENNReal Set

namespace Autocorr.C30

/-- Essential-supremum form: for every measurable `f : ℝ → [0, ∞]`,
`33/25 · (∫_{-1/4}^{1/4} f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (`essSup`; at most the pointwise supremum). -/
theorem autocorr_lower_ess (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (33 / 25 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  rw [← ofReal_lam]
  exact autocorr_lower_ess_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

/-- Real-valued form with Mathlib's convolution: for `f : ℝ → ℝ` measurable, nonnegative and vanishing outside
`[-1/4, 1/4]`, `33/25 · (∫ f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (the norm in `ℝ≥0∞`). -/
theorem autocorr_lower_real (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal (33 / 25 * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  have h := autocorr_lower_real_of_halfClaim (by norm_num) (by positivity) halfClaim f hf hf0 hsupp
  convert h using 3 <;> norm_num

end Autocorr.C30
