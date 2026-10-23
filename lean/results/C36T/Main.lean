-- Excerpt of the generated top module Autocorr.C36T.Gro.Groot: the statements and proofs of the bound.
-- The module also holds the covered theorems of the 620 jobs at the top of the certificate tree and imports
-- Autocorr.Cert.SoundX, Autocorr.RealForm, the table module, 64 check modules and the 6,372 shard subtree roots.

/-! The bound (formerly Autocorr.C36T.Main and Autocorr.C36T.Forms; merged so that the import closure is loaded once). -/

open MeasureTheory ENNReal Set

namespace Autocorr.C36T

theorem rootOK : (Autocorr.Cert.rootBox (Autocorr.Cert.mkSpec 36)).isSome = true := by native_decide

theorem halfClaim : HalfClaim 36 (((133 / 100 : ℚ)) : ℝ) :=
  Autocorr.Cert.halfClaim_of_coveredX Autocorr.C36T.Jroot.covered rootOK

lemma ofReal_lam : ENNReal.ofReal (((133 / 100 : ℚ)) : ℝ) = (133 / 100 : ℝ≥0∞) := by
  rw [show (((133 / 100 : ℚ)) : ℝ) = (133 : ℝ) / 100 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 133/100`: for every measurable `f : ℝ → [0, ∞]`,
`133/100 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx`. -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (133 / 100 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by norm_num) halfClaim f hf


/-- Essential-supremum form: for every measurable `f : ℝ → [0, ∞]`,
`133/100 · (∫_{-1/4}^{1/4} f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (`essSup`; at most the pointwise supremum). -/
theorem autocorr_lower_ess (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (133 / 100 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  rw [← ofReal_lam]
  exact autocorr_lower_ess_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

/-- Real-valued form with Mathlib's convolution: for `f : ℝ → ℝ` measurable, nonnegative and vanishing outside
`[-1/4, 1/4]`, `133/100 · (∫ f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}` (the norm in `ℝ≥0∞`). -/
theorem autocorr_lower_real (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal (133 / 100 * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  have h := autocorr_lower_real_of_halfClaim (by norm_num) (by positivity) halfClaim f hf hf0 hsupp
  convert h using 3 <;> norm_num

end Autocorr.C36T

