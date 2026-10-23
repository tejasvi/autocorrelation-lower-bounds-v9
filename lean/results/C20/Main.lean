import Autocorr.C20.G000.G000000
import Autocorr.Cert.CoveredSound

/-!
# The certificate `c20_128` (n = 20, lam = 32/25) checked in Lean

425 jobs in 355 modules (one `native_decide` per job), composed through `Autocorr.Cert.Covered`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.C20

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 20)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 20 (((32 / 25 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_covered Autocorr.C20.J0.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((32 / 25 : ℚ)) : ℝ) = (32 / 25 : ℝ≥0∞) := by
  rw [show (((32 / 25 : ℚ)) : ℝ) = (32 : ℝ) / 25 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 32/25`: for every measurable `f : ℝ → [0, ∞]`,
`32/25 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (32 / 25 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end Autocorr.C20
