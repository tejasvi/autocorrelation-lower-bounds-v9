import Autocorr.C24.J000.J000000
import Autocorr.Cert.CoveredSound

/-!
# The certificate `cert/c24_130` (n = 24, lam = 13/10) checked in Lean

13974 job modules (one `native_decide` each), composed through `Autocorr.Cert.Covered`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.C24

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 24)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 24 (((13 / 10 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_covered Autocorr.C24.J000.J000000.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((13 / 10 : ℚ)) : ℝ) = (13 / 10 : ℝ≥0∞) := by
  rw [show (((13 / 10 : ℚ)) : ℝ) = (13 : ℝ) / 10 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 13/10`: for every measurable `f : ℝ → [0, ∞]`,
`13/10 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (13 / 10 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end Autocorr.C24
