/-! The bound (generated as Autocorr.KC36.Main and Autocorr.KC36.Forms; merged here so that the import closure is loaded once). -/

open MeasureTheory ENNReal Set

namespace Autocorr.KC36

noncomputable def UP : ℕ := nat_b64% "AAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEA="

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P 0 0 UP = jb_root := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec 36) P := AutocorrK.kpFacts kpok

theorem halfClaim : HalfClaim 36 (((133 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull_root).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec 36).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec 36).n = 36 := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

lemma ofReal_lam : ENNReal.ofReal (((133 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) = (133 / 100 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 133/100`: for every measurable `f : ℝ → [0, ∞]`,
`133/100 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx` (kernel-checked certificate). -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (133 / 100 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by positivity) halfClaim f hf


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

end Autocorr.KC36
