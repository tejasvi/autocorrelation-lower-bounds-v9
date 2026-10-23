import Autocorr.KC20.G000.G000000
import Autocorr.KSound.Run
import Autocorr.Reduction

/-!
# The certificate `cert/c20_128` (n = 20, lam = 32/25) checked by the Lean kernel

425 jobs, 113761 leaves, in 425 core-only modules; every segment of the DFS log is a
`decide +kernel` check of `AutocorrK.segCheck` (no native code), composed by `AutocorrK.StkK`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.KC20

noncomputable def UP : ℕ := nat_b64% "AAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABAAAAAQAAAAEAAAABA"

theorem hupP : ∀ b < P.nB, AutocorrK.get32 UP b = 2 ^ 30 := by decide +kernel

theorem root_eq : AutocorrK.propK P 0 0 UP = jb0 := by decide +kernel

theorem kpf : AutocorrK.KPFacts (Autocorr.Cert.mkSpec 20) P := AutocorrK.kpFacts kpok

theorem halfClaim : HalfClaim 20 (((32 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) := by
  have h := (AutocorrK.stkK_sound kpf (by norm_num) (by norm_num) jfull0).head
  rw [← root_eq] at h
  have hup : ∀ b < (Autocorr.Cert.mkSpec 20).nB, AutocorrK.get32 UP b = 2 ^ 30 := by
    rw [← kpf.nB]; exact hupP
  have hn : (Autocorr.Cert.mkSpec 20).n = 20 := by rw [← kpf.n]; rfl
  have := AutocorrK.halfClaim_of_rootK kpf hup h
  rwa [hn] at this

lemma ofReal_lam : ENNReal.ofReal (((32 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = (32 / 25 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- `C₁ ≥ 32/25`: for every measurable `f : ℝ → [0, ∞]`,
`32/25 · (∫_{-1/4}^{1/4} f)² ≤ sup_{t ∈ [-1/2, 1/2]} ∫ f(t - x) f(x) dx` (kernel-checked certificate). -/
theorem autocorr_lower (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (32 / 25 : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x := by
  rw [← ofReal_lam]
  exact autocorr_lower_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

end Autocorr.KC20
