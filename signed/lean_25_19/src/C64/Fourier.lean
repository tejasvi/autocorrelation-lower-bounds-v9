import C64.CertProp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod
import C64.Defs

/-!
# Fourier–Laplace transforms on `[-1/2, 1/2]` (paper Section 6, equation (6.1))

* `norm_Kt`, `norm_Kt_le`: `|K_t(z)| = e^{2π t Im z} ≤ e^{π |Im z|}` for `|t| ≤ 1/2`;
* `S_eq_integral`: `S(z) = ∫_{-1/2}^{1/2} K_t(z) dt`;
* `continuous_hat`: `μ̂` is continuous for finite measures carried by `[-1/2, 1/2]`.
-/

open MeasureTheory Set Complex Real Filter Topology

namespace C64

lemma norm_Kt (t : ℝ) (z : ℂ) : ‖Kt t z‖ = Real.exp (2 * π * t * z.im) := by
  rw [Kt, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma norm_Kt_le {t : ℝ} (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) (z : ℂ) : ‖Kt t z‖ ≤ Real.exp (π * |z.im|) := by
  rw [norm_Kt]
  apply Real.exp_le_exp.2
  have h1 : |t| ≤ 1/2 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
  have h2 : 2 * π * t * z.im ≤ 2 * π * |t| * |z.im| := by
    have : t * z.im ≤ |t| * |z.im| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith [Real.pi_pos]
  have h3 : 2 * π * |t| * |z.im| ≤ π * |z.im| := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1/2 - |t|) (abs_nonneg z.im)
    nlinarith [Real.pi_pos]
  linarith

lemma continuous_Kt (t : ℝ) : Continuous (Kt t) := by
  unfold Kt; fun_prop

lemma continuous_Kt_t (z : ℂ) : Continuous (fun t : ℝ => Kt t z) := by
  unfold Kt; fun_prop

/-- `S(z) = ∫_{-1/2}^{1/2} K_t(z) dt`. -/
theorem S_eq_integral (z : ℂ) : S z = ∫ t in (-1/2 : ℝ)..(1/2), Kt t z := by
  by_cases hz : z = 0
  · subst hz; simp [S, Kt]; norm_num
  · have hc : (-2 * π * I * z : ℂ) ≠ 0 := by
      simp [hz, Real.pi_ne_zero, Complex.I_ne_zero]
    have : ∀ t : ℝ, Kt t z = Complex.exp ((-2 * π * I * z) * t) := fun t => by
      rw [Kt]; congr 1; ring
    simp_rw [this]
    rw [integral_exp_mul_complex hc, S]
    simp only [hz, ite_false, Complex.sin]
    have hpz : (π * z : ℂ) ≠ 0 := by simp [hz, Real.pi_ne_zero]
    field_simp
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring

/-- `μ̂` is continuous for a finite measure carried by `[-1/2, 1/2]`. -/
theorem continuous_hat {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ (Icc (-1/2 : ℝ) (1/2))ᶜ = 0) :
    Continuous (hat μ) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have hae : ∀ᵐ t ∂μ, t ∈ Icc (-1/2 : ℝ) (1/2) := ae_iff.2 hμ
  refine continuousAt_of_dominated (bound := fun _ => Real.exp (π * (|z₀.im| + 1))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun z => (continuous_Kt_t z).aestronglyMeasurable)
  · have hball : ∀ᶠ z in 𝓝 z₀, |z.im| ≤ |z₀.im| + 1 := by
      have : ∀ᶠ z in 𝓝 z₀, dist z z₀ < 1 := Metric.ball_mem_nhds z₀ one_pos
      filter_upwards [this] with z hz
      have h1 : |z.im - z₀.im| ≤ dist z z₀ := by
        rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm _).trans_eq' (by simp)
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    filter_upwards [hball] with z hz
    filter_upwards [hae] with t ht
    refine (norm_Kt_le ht z).trans (Real.exp_le_exp.2 ?_)
    nlinarith [Real.pi_pos]
  · exact integrable_const _
  · exact Eventually.of_forall (fun t => (continuous_Kt t).continuousAt)

/-! ### The Fourier–Laplace transform of `f` and of `f ⋆ f` -/

/-- `F(z) = ∫ f(x) K_x(z) dx`. -/
noncomputable def FT (f : ℝ → ℝ) (z : ℂ) : ℂ := ∫ x, (f x : ℂ) * Kt x z

lemma Kt_add (s u : ℝ) (z : ℂ) : Kt (s + u) z = Kt s z * Kt u z := by
  simp only [Kt, ← Complex.exp_add]; congr 1; push_cast; ring

lemma admissible_ae {f : ℝ → ℝ} (hf : Admissible f) : ∀ᵐ x ∂(volume : Measure ℝ), f x ≠ 0 → x ∈ Icc (-1/4 : ℝ) (1/4) := by
  filter_upwards [hf.2] with x hx h0
  by_contra hn; exact h0 (hx hn)

/-- `f K(z)` is integrable for admissible `f`. -/
lemma integrable_fK {f : ℝ → ℝ} (hf : Admissible f) (z : ℂ) :
    Integrable (fun x => (f x : ℂ) * Kt x z) := by
  have hmeas : AEStronglyMeasurable (fun x => (f x : ℂ) * Kt x z) volume :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1.aestronglyMeasurable).mul
      (continuous_Kt_t z).aestronglyMeasurable
  refine Integrable.mono' (hf.1.norm.mul_const (Real.exp (π * |z.im|))) hmeas ?_
  filter_upwards [admissible_ae hf] with x hx
  rw [norm_mul, Complex.norm_real]
  by_cases h0 : f x = 0
  · simp [h0]
  · have hxI := hx h0
    have hx2 : x ∈ Icc (-1/2 : ℝ) (1/2) := ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    exact mul_le_mul_of_nonneg_left (norm_Kt_le hx2 z) (norm_nonneg _)

/-- The twisted convolution identity: `(f ⋆ f)(t) K_t(z) = ((f K) ⋆ (f K))(t)`. -/
lemma autoconv_mul_Kt (f : ℝ → ℝ) (z : ℂ) (t : ℝ) :
    (autoconv f t : ℂ) * Kt t z =
      convolution (fun x => (f x : ℂ) * Kt x z) (fun x => (f x : ℂ) * Kt x z)
        (ContinuousLinearMap.mul ℂ ℂ) volume t := by
  rw [convolution_def, autoconv, convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  have : ∀ s : ℝ, (f s : ℂ) * Kt s z * ((f (t - s) : ℂ) * Kt (t - s) z) =
      ((f s * f (t - s) : ℝ) : ℂ) * Kt t z := fun s => by
    have hK : Kt s z * Kt (t - s) z = Kt t z := by rw [← Kt_add]; congr 1; ring
    push_cast
    rw [← hK]; ring
  simp_rw [this]
  rw [integral_mul_const, integral_complex_ofReal]

/-- Paper equation (6.1): `∫ (f ⋆ f)(t) K_t(z) dt = F(z)²`. -/
theorem integral_autoconv_Kt {f : ℝ → ℝ} (hf : Admissible f) (z : ℂ) :
    ∫ t, (autoconv f t : ℂ) * Kt t z = FT f z ^ 2 := by
  simp_rw [autoconv_mul_Kt]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_fK hf z) (integrable_fK hf z)]
  simp [FT, sq]

/-- `f ⋆ f` vanishes outside `[-1/2, 1/2]`. -/
theorem autoconv_eq_zero {f : ℝ → ℝ} (hf : Admissible f) {t : ℝ} (ht : t ∉ Icc (-1/2 : ℝ) (1/2)) :
    autoconv f t = 0 := by
  rw [autoconv, convolution_def]
  apply integral_eq_zero_of_ae
  have h1 := admissible_ae hf
  have h2 : ∀ᵐ s ∂(volume : Measure ℝ), f (t - s) ≠ 0 → t - s ∈ Icc (-1/4 : ℝ) (1/4) :=
    (quasiMeasurePreserving_sub_left volume t).ae h1
  filter_upwards [h1, h2] with s hs1 hs2
  simp only [ContinuousLinearMap.mul_apply', Pi.zero_apply]
  by_contra hne
  have ha : f s ≠ 0 := fun h => hne (by simp [h])
  have hb : f (t - s) ≠ 0 := fun h => hne (by simp [h])
  have hsI := hs1 ha
  have htI := hs2 hb
  apply ht
  constructor <;> linarith [hsI.1, hsI.2, htI.1, htI.2]

lemma integrable_autoconv {f : ℝ → ℝ} (hf : Admissible f) : Integrable (autoconv f) :=
  hf.1.integrable_convolution _ hf.1

/-- `∫ f ⋆ f = (∫ f)²`. -/
theorem integral_autoconv {f : ℝ → ℝ} (hf : Admissible f) : ∫ t, autoconv f t = (∫ x, f x) ^ 2 := by
  have h := integral_autoconv_Kt hf 0
  simp only [Kt, mul_zero, Complex.exp_zero, mul_one, FT] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

/-- `F` is continuous. -/
theorem continuous_FT {f : ℝ → ℝ} (hf : Admissible f) : Continuous (FT f) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  refine continuousAt_of_dominated (bound := fun x => ‖f x‖ * Real.exp (π * (|z₀.im| + 1))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (fun z => (integrable_fK hf z).aestronglyMeasurable)
  · have hball : ∀ᶠ z in 𝓝 z₀, |z.im| ≤ |z₀.im| + 1 := by
      have : ∀ᶠ z in 𝓝 z₀, dist z z₀ < 1 := Metric.ball_mem_nhds z₀ one_pos
      filter_upwards [this] with z hz
      have h1 : |z.im - z₀.im| ≤ dist z z₀ := by
        rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm _).trans_eq' (by simp)
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    filter_upwards [hball] with z hz
    filter_upwards [admissible_ae hf] with x hx
    rw [norm_mul, Complex.norm_real]
    by_cases h0 : f x = 0
    · simp [h0]
    · have hxI := hx h0
      have hx2 : x ∈ Icc (-1/2 : ℝ) (1/2) := ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
      refine mul_le_mul_of_nonneg_left ((norm_Kt_le hx2 z).trans (Real.exp_le_exp.2 ?_)) (norm_nonneg _)
      nlinarith [Real.pi_pos]
  · exact hf.1.norm.mul_const _
  · exact Eventually.of_forall (fun x => ((continuous_const.mul (continuous_Kt x))).continuousAt)

/-! ### The measure `w = 1_{[-1/2,1/2]} - (f ⋆ f)/M` -/

/-- The density `w = 1_{[-1/2,1/2]} - (f ⋆ f)/M`. -/
noncomputable def wden (f : ℝ → ℝ) (M : ℝ) (t : ℝ) : ℝ :=
  (Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => (1 : ℝ)) t - autoconv f t / M

/-- The measure `w(t) dt`. -/
noncomputable def wmeas (f : ℝ → ℝ) (M : ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (wden f M t))

section WMeas

variable {f : ℝ → ℝ} {M : ℝ} (hf : Admissible f) (hint : ∫ x, f x = 1)
  (hM : ∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ M)
include hf hint hM

lemma one_le_M : 1 ≤ M := by
  have hI : Integrable ((Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => M)) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hle : ∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ (Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => M) t := by
    filter_upwards [hM] with t ht
    by_cases htI : t ∈ Icc (-1/2 : ℝ) (1/2)
    · rw [indicator_of_mem htI]; exact ht
    · rw [indicator_of_notMem htI, autoconv_eq_zero hf htI]
  have h1 := integral_mono_ae (integrable_autoconv hf) hI hle
  rw [integral_autoconv hf, hint, integral_indicator_const _ measurableSet_Icc] at h1
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul] at h1
  norm_num at h1
  linarith

lemma M_pos : 0 < M := lt_of_lt_of_le one_pos (one_le_M hf hint hM)

lemma wden_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Icc (-1/2 : ℝ) (1/2)) : wden f M t = 0 := by
  simp only [wden, indicator_of_notMem ht, autoconv_eq_zero hf ht]; simp

lemma wden_nonneg : ∀ᵐ t ∂(volume : Measure ℝ), 0 ≤ wden f M t := by
  filter_upwards [hM] with t ht
  by_cases htI : t ∈ Icc (-1/2 : ℝ) (1/2)
  · simp only [wden, indicator_of_mem htI]
    have := M_pos hf hint hM
    rw [sub_nonneg, div_le_one this]; exact ht
  · rw [wden_eq_zero_of_notMem hf hint hM htI]

omit hint hM in
lemma integrable_ind1 : Integrable ((Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => (1 : ℝ))) :=
  (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc

omit hint hM in
lemma integrable_wden : Integrable (wden f M) :=
  (integrable_ind1 hf).sub ((integrable_autoconv hf).div_const M)

lemma integral_wden : ∫ t, wden f M t = 1 - 1 / M := by
  have : (fun t => wden f M t) = fun t => (Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => (1 : ℝ)) t - autoconv f t / M :=
    rfl
  rw [this, integral_sub (integrable_ind1 hf) ((integrable_autoconv hf).div_const M),
    integral_indicator_const _ measurableSet_Icc, integral_div, integral_autoconv hf, hint]
  simp [Measure.real, Real.volume_Icc]
  norm_num

/-- `w` lies in the class `𝒜_{1 - 1/M}`. -/
theorem classA_wmeas : ClassA (1 - 1 / M) (wmeas f M) := by
  refine ⟨isFiniteMeasure_withDensity_ofReal (integrable_wden (M := M) hf).2, ?_, ?_⟩
  · rw [wmeas, withDensity_apply _ measurableSet_Icc.compl]
    rw [setLIntegral_congr_fun measurableSet_Icc.compl (fun t ht => by
      rw [wden_eq_zero_of_notMem hf hint hM ht, ENNReal.ofReal_zero])]
    simp
  · rw [wmeas, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_wden (M := M) hf) (wden_nonneg hf hint hM),
      integral_wden hf hint hM]

/-- `ŵ(z) = S(z) - F(z)²/M`. -/
theorem hat_wmeas (z : ℂ) : hat (wmeas f M) z = S z - FT f z ^ 2 / M := by
  have hmeas : AEMeasurable (fun t => ENNReal.ofReal (wden f M t)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (integrable_wden (M := M) hf).aemeasurable
  rw [hat, wmeas, integral_withDensity_eq_integral_toReal_smul₀ hmeas
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  set ind : ℝ → ℝ := (Icc (-1/2 : ℝ) (1/2)).indicator (fun _ => (1 : ℝ)) with hind
  have hcongr : (fun t => (ENNReal.ofReal (wden f M t)).toReal • Kt t z) =ᵐ[volume]
      (fun t => ((ind t : ℝ) : ℂ) * Kt t z - ((1 / M : ℝ) : ℂ) * ((autoconv f t : ℂ) * Kt t z)) := by
    filter_upwards [wden_nonneg hf hint hM] with t ht
    rw [ENNReal.toReal_ofReal ht, Complex.real_smul]
    simp only [wden, hind]
    push_cast; ring
  rw [integral_congr_ae hcongr]
  have hind' : (fun t => ((ind t : ℝ) : ℂ) * Kt t z) = (Icc (-1/2 : ℝ) (1/2)).indicator (fun t => Kt t z) := by
    ext t
    by_cases h : t ∈ Icc (-1/2 : ℝ) (1/2)
    · rw [hind, indicator_of_mem h, indicator_of_mem h]; simp
    · rw [hind, indicator_of_notMem h, indicator_of_notMem h]; simp
  have hI1 : Integrable (fun t => ((ind t : ℝ) : ℂ) * Kt t z) := by
    rw [hind']
    exact ((continuous_Kt_t z).continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc
  have hI2 : Integrable (fun t => (autoconv f t : ℂ) * Kt t z) := by
    have : (fun t => (autoconv f t : ℂ) * Kt t z) =
        convolution (fun x => (f x : ℂ) * Kt x z) (fun x => (f x : ℂ) * Kt x z)
          (ContinuousLinearMap.mul ℂ ℂ) volume := funext (autoconv_mul_Kt f z)
    rw [this]; exact (integrable_fK hf z).integrable_convolution _ (integrable_fK hf z)
  rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul, integral_autoconv_Kt hf]
  have hS : ∫ t, ((ind t : ℝ) : ℂ) * Kt t z = S z := by
    rw [hind', S_eq_integral, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      integral_indicator measurableSet_Icc]
  rw [hS]; push_cast; ring

/-- `G_w = F²/M`. -/
theorem G_wmeas (z : ℂ) : G (wmeas f M) z = FT f z ^ 2 / M := by
  rw [G, hat_wmeas hf hint hM]; ring

end WMeas

end C64
