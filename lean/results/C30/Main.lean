import Autocorr.C30.G000.G000000
import Autocorr.Cert.SoundX

/-!
# The certificate `cert/c30_132m` (n = 30, lam = 33/25) checked in Lean

290308 jobs in 67740 modules (one `native_decide` per job, extended checker `checkJobStrX` with square
cuts and compressed leaves), composed through `Autocorr.Cert.CoveredX`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.C30

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 30)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 30 (((33 / 25 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_coveredX Autocorr.C30.J0.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((33 / 25 : ℚ)) : ℝ) = (33 / 25 : ℝ≥0∞) := by
  rw [show (((33 / 25 : ℚ)) : ℝ) = (33 : ℝ) / 25 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 33/25`: for every measurable `f : ℝ → [0, ∞]`,
`33/25 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (33 / 25 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf

end Autocorr.C30
