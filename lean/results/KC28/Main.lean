import Autocorr.KC28.G000.G000000
import Autocorr.KSound.Run
import Autocorr.Reduction

/-!
# The certificate `cert/c28_131` (n = 28, lam = 131/100) checked by the Lean kernel

322266 jobs, 15250196 leaves, in 2 x 43140 core-only modules; every segment of the DFS log is a
`decide +kernel` check of `AutocorrK.segCheck` (no native code), composed by `AutocorrK.StkK`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.KC28

noncomputable def UP : ℕ := nat_b64% "AAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQA=="

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P 0 0 UP = jb0 := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec 28) P := AutocorrK.kpFacts kpok

theorem halfClaim : HalfClaim 28 (((131 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull0).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec 28).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec 28).n = 28 := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

lemma ofReal_lam : ENNReal.ofReal (((131 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)) = (131 / 100 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 131/100`: for every measurable `f : ℝ → [0, ∞]`,
`131/100 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx` (kernel-checked certificate). -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (131 / 100 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

end Autocorr.KC28
