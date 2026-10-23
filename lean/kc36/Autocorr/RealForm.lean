import Autocorr.Reduction
import Mathlib.Analysis.Convolution

/-!
# The real-valued form of the bound

For `f : ℝ → ℝ` measurable, nonnegative and vanishing outside `[-1/4, 1/4]`:

  `lam · (∫ f)² ≤ ‖f ⋆ f‖_{L^∞(-1/2, 1/2)}`,

with Mathlib's convolution `f ⋆ f` (`(f ⋆ f)(t) = ∫ f(s) f(t - s) ds`) and the `L^∞` norm (essential supremum)
on `[-1/2, 1/2]`, taken in `ℝ≥0∞` (it may be infinite).  If `f` is not integrable, `∫ f = 0` (Bochner
convention) and the bound is trivial; otherwise the Bochner and Lebesgue autoconvolutions agree almost
everywhere and the bound is `autocorr_lower_ess_of_halfClaim` for `ofReal ∘ f`.
-/

open MeasureTheory ENNReal Set

namespace Autocorr

theorem autocorr_lower_real_of_halfClaim {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : HalfClaim n lam) (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal (lam * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  by_cases hint : Integrable f
  swap
  · rw [integral_undef hint]; simp
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hF
  have hFm : Measurable F := hf.ennreal_ofReal
  -- the mass
  have hmass : ENNReal.ofReal (∫ x, f x) = ∫⁻ x in Icc (-1/4 : ℝ) (1/4), F x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      ofReal_integral_eq_lintegral_ofReal hint.integrableOn (ae_of_all _ (fun x => hf0 x))]
  have hlhs : ENNReal.ofReal (lam * (∫ x, f x) ^ 2) =
      ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), F x) ^ 2 := by
    rw [ENNReal.ofReal_mul hlam, ENNReal.ofReal_pow (integral_nonneg hf0), hmass]
  -- the autoconvolution, almost everywhere
  have hconv : ∀ᵐ t ∂(volume : Measure ℝ),
      ‖convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume t‖ₑ = ∫⁻ x, F (t - x) * F x := by
    filter_upwards [hint.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hint] with t ht
    have hval : convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume t = ∫ s, f s * f (t - s) := by
      simp [convolution_def]
    have hnn : 0 ≤ convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume t := by
      rw [hval]; exact integral_nonneg (fun s => mul_nonneg (hf0 s) (hf0 (t - s)))
    have hi : Integrable (fun s => f s * f (t - s)) := by
      simpa [ConvolutionExistsAt] using ht
    rw [Real.enorm_eq_ofReal hnn, hval,
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun s => mul_nonneg (hf0 s) (hf0 (t - s))))]
    have e : ∀ s, ENNReal.ofReal (f s * f (t - s)) = F (t - (t - s)) * F (t - s) := by
      intro s
      show ENNReal.ofReal (f s * f (t - s)) = ENNReal.ofReal (f (t - (t - s))) * ENNReal.ofReal (f (t - s))
      rw [_root_.sub_sub_cancel, ENNReal.ofReal_mul (hf0 s)]
    simp_rw [e]
    exact lintegral_sub_left_eq_self (fun x => F (t - x) * F x) t
  have hmeas : AEStronglyMeasurable (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) :=
    (hint.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hint).aestronglyMeasurable.restrict
  rw [hlhs, eLpNorm_exponent_top hmeas, eLpNormEssSup,
    essSup_congr_ae (ae_restrict_of_ae hconv)]
  exact autocorr_lower_ess_of_halfClaim hn hlam hH F hFm

end Autocorr
