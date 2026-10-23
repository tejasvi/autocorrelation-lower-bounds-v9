import Autocorr.C28.G000.G000000
import Autocorr.Cert.CoveredSound

/-!
# The certificate `cert/c28_131` (n = 28, lam = 131/100) checked in Lean

322266 jobs in 43140 modules (one `native_decide` per job), composed through `Autocorr.Cert.Covered`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.C28

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 28)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 28 (((131 / 100 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_covered Autocorr.C28.J0.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((131 / 100 : ℚ)) : ℝ) = (131 / 100 : ℝ≥0∞) := by
  rw [show (((131 / 100 : ℚ)) : ℝ) = (131 : ℝ) / 100 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 131/100`: for every measurable `f : ℝ → [0, ∞]`,
`131/100 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (131 / 100 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end Autocorr.C28
