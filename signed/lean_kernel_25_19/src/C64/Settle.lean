import C64.Reduction
import C64.SDeriv

/-!
# Settled arcs (paper Lemmas 6.3-6.5, Definition 6.6), in the form the checker establishes

* `integral_le_of_classA` (Lemma 6.3(a)): `∫ φ dμ ≤ τ B` when `φ ≤ B` on `[-1/2, 1/2]`, `B ≥ 0`, `μ ∈ 𝒜_τ`;
* `re_conj_mul_hat`: `Re(ū μ̂(z)) = ∫ Re(ū K_t(z)) dμ(t)`;
* `settled_E`: an arc on which `Re(ū S) > 0` and `τ Re(ū K_t) < Re(ū S)` for all `t` is settled (no crossing).
-/

open MeasureTheory Set Complex Real Filter Topology ComplexConjugate

namespace C64

section ClassALemmas

variable {τ : ℝ} {μ : Measure ℝ}

lemma ClassA.ae_mem (h : ClassA τ μ) : ∀ᵐ t ∂μ, t ∈ Icc (-1/2 : ℝ) (1/2) := ae_iff.2 h.2.1

lemma integrable_Kt_of_classA (h : ClassA τ μ) (z : ℂ) : Integrable (fun t => Kt t z) μ := by
  have := h.1
  refine Integrable.mono' (integrable_const (Real.exp (π * |z.im|))) (continuous_Kt_t z).aestronglyMeasurable ?_
  filter_upwards [h.ae_mem] with t ht
  exact norm_Kt_le ht z

lemma re_conj_mul_hat (h : ClassA τ μ) (u z : ℂ) :
    (conj u * hat μ z).re = ∫ t, (conj u * Kt t z).re ∂μ := by
  rw [hat, ← integral_const_mul]
  have := Complex.reCLM.integral_comp_comm ((integrable_Kt_of_classA h z).const_mul (conj u))
  simpa using this.symm

lemma mass_le (h : ClassA τ μ) (hτ : 0 ≤ τ) : μ.real univ ≤ τ := by
  have := h.1
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal hτ h.2.2

/-- Lemma 6.3(a): `∫ φ dμ ≤ τ B` for `μ ∈ 𝒜_τ`, `φ ≤ B` on `[-1/2, 1/2]` and `B ≥ 0`. -/
theorem integral_le_of_classA (h : ClassA τ μ) (hτ : 0 ≤ τ) {φ : ℝ → ℝ} (hφ : Integrable φ μ) {B : ℝ}
    (hB : 0 ≤ B) (hφB : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), φ t ≤ B) : ∫ t, φ t ∂μ ≤ τ * B := by
  have := h.1
  have h1 : ∫ t, φ t ∂μ ≤ ∫ _t, B ∂μ := by
    refine integral_mono_ae hφ (integrable_const B) ?_
    filter_upwards [h.ae_mem] with t ht
    exact hφB t ht
  rw [integral_const, smul_eq_mul] at h1
  have h2 : μ.real univ * B ≤ τ * B := mul_le_mul_of_nonneg_right (mass_le h hτ) hB
  linarith

lemma integrable_re_conj_mul_Kt (h : ClassA τ μ) (u z : ℂ) :
    Integrable (fun t => (conj u * Kt t z).re) μ :=
  ((integrable_Kt_of_classA h z).const_mul _).re

end ClassALemmas

/-- The maximum of a continuous function of `t` on `[-1/2, 1/2]`. -/
lemma exists_max_on_Icc {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∃ t₀ ∈ Icc (-1/2 : ℝ) (1/2), ∀ t ∈ Icc (-1/2 : ℝ) (1/2), φ t ≤ φ t₀ := by
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc : IsCompact (Icc (-1/2 : ℝ) (1/2))).exists_isMaxOn
    (nonempty_Icc.2 (by norm_num)) hφ.continuousOn
  exact ⟨t₀, ht₀, fun t ht => hmax ht⟩

lemma continuous_re_conj_mul_Kt (u z : ℂ) : Continuous (fun t : ℝ => (conj u * Kt t z).re) :=
  Complex.continuous_re.comp (continuous_const.mul (continuous_Kt_t z))

/-- A point with `Re(ū S(z)) > 0` and `τ Re(ū K_t(z)) < Re(ū S(z))` for all `t` is not a crossing. -/
theorem no_crossing_of_sep {τ : ℝ} (hτ : 0 ≤ τ) {u z : ℂ} (hpos : 0 < (conj u * S z).re)
    (hsep : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * (conj u * Kt t z).re < (conj u * S z).re)
    {μ : Measure ℝ} (hμ : ClassA τ μ) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1)
    (hcr : S z = lam * hat μ z) : False := by
  set A := (conj u * S z).re
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc (continuous_re_conj_mul_Kt u z)
  set B := max 0 (conj u * Kt t₀ z).re
  have hB0 : 0 ≤ B := le_max_left _ _
  have hint := integral_le_of_classA hμ hτ (integrable_re_conj_mul_Kt hμ u z) hB0
    (fun t ht => (hmax t ht).trans (le_max_right _ _))
  have hτB : τ * B < A := by
    rcases le_total (conj u * Kt t₀ z).re 0 with h | h
    · have : B = 0 := max_eq_left h
      rw [this, mul_zero]; exact hpos
    · have : B = (conj u * Kt t₀ z).re := max_eq_right h
      rw [this]; exact hsep t₀ ht₀
  have hA : A = lam * ∫ t, (conj u * Kt t z).re ∂μ := by
    simp only [A, hcr]
    rw [show conj u * (↑lam * hat μ z) = (lam : ℂ) * (conj u * hat μ z) by ring, Complex.re_ofReal_mul,
      re_conj_mul_hat hμ]
  -- A = λ ∫ ≤ τ B < A
  rcases le_total (∫ t, (conj u * Kt t z).re ∂μ) 0 with h | h
  · have : A ≤ 0 := by rw [hA]; exact mul_nonpos_of_nonneg_of_nonpos hlam.1.le h
    linarith
  · have : A ≤ ∫ t, (conj u * Kt t z).re ∂μ := by
      rw [hA]; exact mul_le_of_le_one_left h hlam.2
    have hτB0 : 0 ≤ τ * B := mul_nonneg hτ hB0
    linarith

/-- Type E arcs (Definition 6.6(ii), one-sided case): separation on the whole arc settles it. -/
theorem settled_E {τ c a b s₀ s₁ : ℝ} (hτ : 0 ≤ τ) {u : ℂ}
    (hE : ∀ s ∈ Icc s₀ s₁, 0 < (conj u * S (ellipse c a b s)).re ∧
      ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * (conj u * Kt t (ellipse c a b s)).re < (conj u * S (ellipse c a b s)).re) :
    ArcSettled τ c a b s₀ s₁ := by
  intro μ hμ s hs lam hlam hcr
  exact (no_crossing_of_sep hτ (hE s hs).1 (hE s hs).2 hμ hlam hcr).elim

/-! ### Localization (Lemma 6.5) -/

lemma norm_hat_le {τ : ℝ} (hτ : 0 ≤ τ) {μ : Measure ℝ} (hμ : ClassA τ μ) (z : ℂ) :
    ‖hat μ z‖ ≤ τ * Real.exp (π * |z.im|) := by
  have := hμ.1
  rw [hat]
  refine (norm_integral_le_of_norm_le (integrable_const (Real.exp (π * |z.im|))) ?_).trans ?_
  · filter_upwards [hμ.ae_mem] with t ht; exact norm_Kt_le ht z
  · rw [integral_const, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (mass_le hμ hτ) (Real.exp_pos _).le

lemma norm_hat_sub_le {τ : ℝ} (hτ : 0 ≤ τ) {μ : Measure ℝ} (hμ : ClassA τ μ) {U : Set ℂ} (hU : Convex ℝ U)
    {Y : ℝ} (hY : ∀ ζ ∈ U, |ζ.im| ≤ Y) {z z' : ℂ} (hz : z ∈ U) (hz' : z' ∈ U) :
    ‖hat μ z - hat μ z'‖ ≤ τ * (π * Real.exp (π * Y) * ‖z - z'‖) := by
  have := hμ.1
  rw [hat, hat, ← integral_sub (integrable_Kt_of_classA hμ z) (integrable_Kt_of_classA hμ z')]
  refine (norm_integral_le_of_norm_le (integrable_const (π * Real.exp (π * Y) * ‖z - z'‖)) ?_).trans ?_
  · filter_upwards [hμ.ae_mem] with t ht; exact norm_sub_Kt_le ht hU hY hz hz'
  · rw [integral_const, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (mass_le hμ hτ) (by positivity)

/-- Lemma 6.5 (localization): a crossing at `z` pins `μ̂(z_c)` to the disc of radius `r_τ` around `σ S(z_c)`. -/
theorem localization {τ : ℝ} (hτ : 0 ≤ τ) {μ : Measure ℝ} (hμ : ClassA τ μ) {zc z : ℂ} {d Y L mS : ℝ}
    (hd : ‖z - zc‖ ≤ d) (hY : ∀ ζ ∈ Metric.closedBall zc d, |ζ.im| ≤ Y)
    (hL : ∀ ζ ∈ Metric.closedBall zc d, ‖S1 ζ‖ ≤ L) (hmS : 0 < mS) (hSz : mS ≤ ‖S z‖)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (hcr : S z = lam * hat μ z) :
    1 ≤ 1 / lam ∧ ‖hat μ zc - ((1 / lam : ℝ) : ℂ) * S zc‖ ≤
      d * (π * τ * Real.exp (π * Y) + τ * Real.exp (π * Y) / mS * L) := by
  have hl0 : 0 < lam := hlam.1
  set σ := 1 / lam with hσ
  have hσ1 : 1 ≤ σ := by rw [hσ, le_div_iff₀ hl0]; linarith [hlam.2]
  refine ⟨hσ1, ?_⟩
  have hzU : z ∈ Metric.closedBall zc d := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hd
  have hcU : zc ∈ Metric.closedBall zc d := Metric.mem_closedBall_self ((norm_nonneg _).trans hd)
  have hU := convex_closedBall zc d
  -- μ̂(z) = σ S(z)
  have hl0' : (lam : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have hmz : hat μ z = (σ : ℂ) * S z := by
    rw [hcr, hσ]; push_cast; field_simp
  -- σ ≤ τ e^{πY}/mS
  have hσmax : σ ≤ τ * Real.exp (π * Y) / mS := by
    have h1 : ‖hat μ z‖ ≤ τ * Real.exp (π * Y) := (norm_hat_le hτ hμ z).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hY z hzU) Real.pi_pos.le)) hτ)
    rw [hmz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < σ)] at h1
    rw [le_div_iff₀ hmS]
    nlinarith [mul_le_mul_of_nonneg_left hSz (by positivity : (0:ℝ) ≤ σ)]
  have h2 := norm_hat_sub_le hτ hμ hU (fun ζ hζ => hY ζ hζ) hcU hzU
  have h3 := norm_sub_S_le hU hL hzU hcU
  have hd' : ‖zc - z‖ ≤ d := by rw [norm_sub_rev]; exact hd
  calc ‖hat μ zc - (σ : ℂ) * S zc‖
      = ‖(hat μ zc - hat μ z) + (σ : ℂ) * (S z - S zc)‖ := by rw [hmz]; ring_nf
    _ ≤ ‖hat μ zc - hat μ z‖ + σ * ‖S z - S zc‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < σ)]
    _ ≤ τ * (π * Real.exp (π * Y) * d) + τ * Real.exp (π * Y) / mS * (L * d) := by
        have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL zc hcU)
        gcongr
        · exact h2.trans (by gcongr)
        · exact h3.trans (mul_le_mul_of_nonneg_left hd hL0)
    _ = d * (π * τ * Real.exp (π * Y) + τ * Real.exp (π * Y) / mS * L) := by ring

/-! ### Pinned sets (Lemma 6.4) and witnesses -/

/-- A closed rectangle `[x₀, x₁] × [y₀, y₁]` in `ℂ`. -/
structure Box where
  x0 : ℝ
  x1 : ℝ
  y0 : ℝ
  y1 : ℝ

def Box.mem (Q : Box) (w : ℂ) : Prop := Q.x0 ≤ w.re ∧ w.re ≤ Q.x1 ∧ Q.y0 ≤ w.im ∧ w.im ≤ Q.y1

/-- `μ` lies in the pinned set `𝒫(τ', z_c, r'; p_1, Q_1; …; p_k, Q_k)`. -/
def Pinned (τ' : ℝ) (zc : ℂ) (r' : ℝ) {k : ℕ} (ps : Fin k → ℂ) (Qs : Fin k → Box) (μ : Measure ℝ) : Prop :=
  ClassA τ' μ ∧ (∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r') ∧ ∀ j, (Qs j).mem (hat μ (ps j))

lemma Pinned.mono {τ τ' r r' : ℝ} {zc : ℂ} {k : ℕ} {ps : Fin k → ℂ} {Qs : Fin k → Box} {μ : Measure ℝ}
    (h : Pinned τ zc r ps Qs μ) (hτ : τ ≤ τ') (hr : r ≤ r') : Pinned τ' zc r' ps Qs μ :=
  ⟨h.1.mono hτ, let ⟨σ, h1, h2⟩ := h.2.1; ⟨σ, h1, h2.trans hr⟩, h.2.2⟩

/-- `Λ(t) = Re(v̄ K_t(z_c)) + Σ_j Re(ȳ_j K_t(p_j))`. -/
noncomputable def Lam (v zc : ℂ) {k : ℕ} (ys ps : Fin k → ℂ) (t : ℝ) : ℝ :=
  (conj v * Kt t zc).re + ∑ j, (conj (ys j) * Kt t (ps j)).re

lemma continuous_Lam (v zc : ℂ) {k : ℕ} (ys ps : Fin k → ℂ) : Continuous (Lam v zc ys ps) := by
  unfold Lam
  exact (continuous_re_conj_mul_Kt v zc).add (continuous_finsetSum _ (fun j _ => continuous_re_conj_mul_Kt _ _))

lemma integral_Lam {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (v zc : ℂ) {k : ℕ} (ys ps : Fin k → ℂ) :
    ∫ t, Lam v zc ys ps t ∂μ = (conj v * hat μ zc).re + ∑ j, (conj (ys j) * hat μ (ps j)).re := by
  unfold Lam
  rw [integral_add (integrable_re_conj_mul_Kt hμ v zc)
    (integrable_finsetSum _ (fun j _ => integrable_re_conj_mul_Kt hμ _ _)),
    integral_finsetSum _ (fun j _ => integrable_re_conj_mul_Kt hμ _ _), re_conj_mul_hat hμ]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (re_conj_mul_hat hμ _ _).symm)

lemma integrable_Lam {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (v zc : ℂ) {k : ℕ} (ys ps : Fin k → ℂ) :
    Integrable (Lam v zc ys ps) μ := by
  unfold Lam
  exact (integrable_re_conj_mul_Kt hμ v zc).add (integrable_finsetSum _ (fun j _ => integrable_re_conj_mul_Kt hμ _ _))

lemma re_conj_mul_ge (v s w : ℂ) (σ : ℝ) {r : ℝ} (h : ‖w - (σ : ℂ) * s‖ ≤ r) :
    σ * (conj v * s).re - ‖v‖ * r ≤ (conj v * w).re := by
  have h1 : |(conj v * (w - (σ : ℂ) * s)).re| ≤ ‖v‖ * r := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  have h2 : (conj v * (w - (σ : ℂ) * s)).re = (conj v * w).re - σ * (conj v * s).re := by
    rw [mul_sub, Complex.sub_re, show conj v * ((σ : ℂ) * s) = (σ : ℂ) * (conj v * s) by ring, Complex.re_ofReal_mul]
  rw [h2] at h1
  linarith [(abs_le.1 h1).1]

lemma re_conj_mul_le (v s w : ℂ) (σ : ℝ) {r : ℝ} (h : ‖w - (σ : ℂ) * s‖ ≤ r) :
    (conj v * w).re ≤ σ * (conj v * s).re + ‖v‖ * r := by
  have h1 : |(conj v * (w - (σ : ℂ) * s)).re| ≤ ‖v‖ * r := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  have h2 : (conj v * (w - (σ : ℂ) * s)).re = (conj v * w).re - σ * (conj v * s).re := by
    rw [mul_sub, Complex.sub_re, show conj v * ((σ : ℂ) * s) = (σ : ℂ) * (conj v * s) by ring, Complex.re_ofReal_mul]
  rw [h2] at h1
  linarith [(abs_le.1 h1).2]

/-- Real-linear bounds on a box: `lo ≤ Re(ȳ x) ≤ hi` for `x ∈ Q`. -/
def BoxBounds (y : ℂ) (Q : Box) (lo hi : ℝ) : Prop := ∀ w, Q.mem w → lo ≤ (conj y * w).re ∧ (conj y * w).re ≤ hi

/-- Lemma 6.4(a) (exclusion): the pinned set is empty. -/
theorem pinned_empty {τ : ℝ} (hτ : 0 ≤ τ) {zc : ℂ} {r : ℝ} {k : ℕ} {ps : Fin k → ℂ} {Qs : Fin k → Box}
    {v : ℂ} {ys : Fin k → ℂ} {los his : Fin k → ℝ} (hbox : ∀ j, BoxBounds (ys j) (Qs j) (los j) (his j))
    (hX : 0 ≤ (conj v * S zc).re)
    (hE : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * Lam v zc ys ps t < (conj v * S zc).re - ‖v‖ * r + ∑ j, los j)
    (hEpos : 0 < (conj v * S zc).re - ‖v‖ * r + ∑ j, los j)
    {μ : Measure ℝ} (hμ : Pinned τ zc r ps Qs μ) : False := by
  obtain ⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩ := hμ
  set E := (conj v * S zc).re - ‖v‖ * r + ∑ j, los j
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc (continuous_Lam v zc ys ps)
  set B := max 0 (Lam v zc ys ps t₀)
  have hB0 : 0 ≤ B := le_max_left _ _
  have hint := integral_le_of_classA hA hτ (integrable_Lam hA v zc ys ps) hB0
    (fun t ht => (hmax t ht).trans (le_max_right _ _))
  have hτB : τ * B < E := by
    rcases le_total (Lam v zc ys ps t₀) 0 with h | h
    · rw [show B = 0 from max_eq_left h, mul_zero]; exact hEpos
    · rw [show B = Lam v zc ys ps t₀ from max_eq_right h]; exact hE t₀ ht₀
  have hlow : E ≤ ∫ t, Lam v zc ys ps t ∂μ := by
    rw [integral_Lam hA]
    have h1 := re_conj_mul_ge v (S zc) (hat μ zc) σ hσr
    have h2 : (σ : ℝ) * (conj v * S zc).re ≥ (conj v * S zc).re := by nlinarith
    have h3 : ∑ j, los j ≤ ∑ j, (conj (ys j) * hat μ (ps j)).re :=
      Finset.sum_le_sum (fun j _ => (hbox j _ (hQ j)).1)
    simp only [E]; linarith
  linarith

/-- Lemma 6.4(b) for convex combinations of two pinned measures: `G` does not vanish at `p`. -/
theorem pinned_tile_ne {τ' : ℝ} (hτ : 0 ≤ τ') {zc : ℂ} {r' : ℝ} {k : ℕ} {ps : Fin k → ℂ} {Qs : Fin k → Box}
    {u v : ℂ} {ys : Fin k → ℂ} {los his : Fin k → ℝ} (hbox : ∀ j, BoxBounds (ys j) (Qs j) (los j) (his j))
    {p : ℂ} (hX : (conj v * S zc).re ≤ 0)
    (hW : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ' * ((conj u * Kt t p).re - Lam v zc ys ps t) <
      (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - ∑ j, his j)
    (hWpos : 0 < (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - ∑ j, his j)
    {μ ν : Measure ℝ} (hμ : Pinned τ' zc r' ps Qs μ) (hν : Pinned τ' zc r' ps Qs ν)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : S p - ((1 - θ) * hat μ p + θ * hat ν p) ≠ 0 := by
  set W := (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - ∑ j, his j
  set φ : ℝ → ℝ := fun t => (conj u * Kt t p).re - Lam v zc ys ps t with hφ
  have hφc : Continuous φ := (continuous_re_conj_mul_Kt u p).sub (continuous_Lam v zc ys ps)
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc hφc
  set B := max 0 (φ t₀)
  have hB0 : 0 ≤ B := le_max_left _ _
  have hτB : τ' * B < W := by
    rcases le_total (φ t₀) 0 with h | h
    · rw [show B = 0 from max_eq_left h, mul_zero]; exact hWpos
    · rw [show B = φ t₀ from max_eq_right h]; exact hW t₀ ht₀
  -- for a pinned measure ρ: Re(ū ρ̂(p)) ≤ τ' B + Re(v̄ S zc) + ‖v‖ r' + Σ his
  have key : ∀ ρ : Measure ℝ, Pinned τ' zc r' ps Qs ρ →
      (conj u * hat ρ p).re ≤ τ' * B + ((conj v * S zc).re + ‖v‖ * r' + ∑ j, his j) := by
    intro ρ ⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩
    have hint := integral_le_of_classA hA hτ (φ := fun t => (conj u * Kt t p).re - Lam v zc ys ps t)
      ((integrable_re_conj_mul_Kt hA u p).sub (integrable_Lam hA v zc ys ps))
      hB0 (fun t ht => (hmax t ht).trans (le_max_right _ _))
    rw [integral_sub (integrable_re_conj_mul_Kt hA u p) (integrable_Lam hA v zc ys ps), ← re_conj_mul_hat hA,
      integral_Lam hA] at hint
    have h1 := re_conj_mul_le v (S zc) (hat ρ zc) σ hσr
    have h2 : (σ : ℝ) * (conj v * S zc).re ≤ (conj v * S zc).re := by nlinarith
    have h3 : ∑ j, (conj (ys j) * hat ρ (ps j)).re ≤ ∑ j, his j :=
      Finset.sum_le_sum (fun j _ => (hbox j _ (hQ j)).2)
    linarith
  intro h0
  have hSp : S p = (1 - θ) * hat μ p + θ * hat ν p := sub_eq_zero.1 h0
  have hre : (conj u * S p).re = (1 - θ) * (conj u * hat μ p).re + θ * (conj u * hat ν p).re := by
    rw [hSp]
    simp only [mul_add, Complex.add_re]
    rw [show conj u * ((1 - (θ : ℂ)) * hat μ p) = ((1 - θ : ℝ) : ℂ) * (conj u * hat μ p) by push_cast; ring,
      show conj u * ((θ : ℂ) * hat ν p) = (θ : ℂ) * (conj u * hat ν p) by ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hk1 := key μ hμ
  have hk2 := key ν hν
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have : (conj u * S p).re ≤ τ' * B + ((conj v * S zc).re + ‖v‖ * r' + ∑ j, his j) := by
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hk1 hθ1, mul_le_mul_of_nonneg_left hk2 hθ0]
  simp only [W] at hτB
  linarith

/-! ### Leaves and arcs of type H -/

/-- Every measure pinned in the leaf has an odd-winding ellipse. -/
def LeafSettled (τ : ℝ) (zc : ℂ) (r : ℝ) {k : ℕ} (ps : Fin k → ℂ) (Qs : Fin k → Box) : Prop :=
  ∀ μ : Measure ℝ, Pinned τ zc r ps Qs μ → OddLoop μ

theorem leafSettled_of_exclusion {τ : ℝ} (hτ : 0 ≤ τ) {zc : ℂ} {r : ℝ} {k : ℕ} {ps : Fin k → ℂ}
    {Qs : Fin k → Box} {v : ℂ} {ys : Fin k → ℂ} {los his : Fin k → ℝ}
    (hbox : ∀ j, BoxBounds (ys j) (Qs j) (los j) (his j)) (hX : 0 ≤ (conj v * S zc).re)
    (hE : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * Lam v zc ys ps t < (conj v * S zc).re - ‖v‖ * r + ∑ j, los j)
    (hEpos : 0 < (conj v * S zc).re - ‖v‖ * r + ∑ j, los j) : LeafSettled τ zc r ps Qs :=
  fun _ hμ => (pinned_empty hτ hbox hX hE hEpos hμ).elim

/-- Lemma 6.6 (witness covers) in winding form. -/
theorem leafSettled_of_witness {τ τ' r r' : ℝ} (hττ' : τ ≤ τ') (hrr' : r ≤ r') {zc : ℂ} {k : ℕ}
    {ps : Fin k → ℂ} {Qs : Fin k → Box} {cT : ℂ} {aT bT : ℝ} (haT : 0 < aT) (hbT : 0 < bT)
    (htile : ∀ q ∈ Icc (0 : ℝ) 1, ∀ μ ν : Measure ℝ, Pinned τ' zc r' ps Qs μ → Pinned τ' zc r' ps Qs ν →
      ∀ θ ∈ Icc (0 : ℝ) 1, S (ellipse cT aT bT q) -
        ((1 - θ) * hat μ (ellipse cT aT bT q) + θ * hat ν (ellipse cT aT bT q)) ≠ 0)
    {ν : Measure ℝ} (hν : Pinned τ' zc r' ps Qs ν) {n : ℤ} (hn : Odd n)
    (hwind : HasWinding (fun q => G ν (ellipse cT aT bT q)) n) : LeafSettled τ zc r ps Qs := by
  intro μ hμ
  have hμ' := hμ.mono hττ' hrr'
  set H : ℝ → ℝ → ℂ := fun θ q => S (ellipse cT aT bT q) -
    (θ * hat μ (ellipse cT aT bT q) + (1 - θ) * hat ν (ellipse cT aT bT q)) with hH
  have hne : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, H θ q ≠ 0 := by
    intro θ hθ q hq
    have := htile q hq μ ν hμ' hν (1 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    simpa [hH, sub_sub_cancel, add_comm] using this
  have hcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    apply Continuous.continuousOn
    have h1 : Continuous fun p : ℝ × ℝ => ellipse cT aT bT p.2 := (continuous_ellipse cT aT bT).comp continuous_snd
    have hμc := continuous_hat_of_classA hμ'.1
    have hνc := continuous_hat_of_classA hν.1
    exact (continuous_S.comp h1).sub (((Complex.continuous_ofReal.comp continuous_fst).mul (hμc.comp h1)).add
      ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul (hνc.comp h1)))
  have hper : ∀ θ ∈ Icc (0 : ℝ) 1, H θ 0 = H θ 1 := fun θ _ => by simp only [hH, ellipse_zero_eq_one]
  have h0 : HasWinding (H 0) n := by
    have : H 0 = fun q => G ν (ellipse cT aT bT q) := by funext q; simp [hH, G]
    rw [this]; exact hwind
  have h1 := hasWinding_homotopy hcont hne hper h0
  refine ⟨cT, aT, bT, haT, hbT, fun q hq => ?_, n, hn, ?_⟩
  · have := hne 1 ⟨zero_le_one, le_rfl⟩ q hq; simpa [hH, G] using this
  · have : H 1 = fun q => G μ (ellipse cT aT bT q) := by funext q; simp [hH, G]
    rw [← this]; exact h1

/-- An arc of type H (levels 2 and 3): localization plus settled leaves covering the possible pinned values. -/
theorem settled_H {τ c a b s₀ s₁ : ℝ} {zc : ℂ} {r : ℝ}
    (hloc : ∀ μ : Measure ℝ, ClassA τ μ → ∀ s ∈ Icc s₀ s₁, ∀ lam ∈ Ioc (0 : ℝ) 1,
      S (ellipse c a b s) = lam * hat μ (ellipse c a b s) → ∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r)
    {k : ℕ} (ps : Fin k → ℂ)
    (hcov : ∀ μ : Measure ℝ, ClassA τ μ → ∃ Qs : Fin k → Box, (∀ j, (Qs j).mem (hat μ (ps j))) ∧
      LeafSettled τ zc r ps Qs) :
    ArcSettled τ c a b s₀ s₁ := by
  intro μ hμ s hs lam hlam hcr
  obtain ⟨σ, hσ1, hσr⟩ := hloc μ hμ s hs lam hlam hcr
  obtain ⟨Qs, hQ, hset⟩ := hcov μ hμ
  exact hset μ ⟨hμ, ⟨σ, hσ1, hσr⟩, hQ⟩

/-- Localization from the checker's numbers: `d ≥ |z - z_c|` on the arc, `|Im| ≤ Y` and `|S'| ≤ L` on the disc
`D(z_c, d)`, `|S| ≥ m_S > 0` on the arc, and `r ≥ d (π τ e^{π Y} + (τ e^{π Y}/m_S) L)`. -/
theorem hloc_of_bounds {τ c a b s₀ s₁ : ℝ} (hτ : 0 ≤ τ) {zc : ℂ} {d Y L mS r : ℝ}
    (hd : ∀ s ∈ Icc s₀ s₁, ‖ellipse c a b s - zc‖ ≤ d) (hY : ∀ ζ ∈ Metric.closedBall zc d, |ζ.im| ≤ Y)
    (hL : ∀ ζ ∈ Metric.closedBall zc d, ‖S1 ζ‖ ≤ L) (hmS : 0 < mS)
    (hSz : ∀ s ∈ Icc s₀ s₁, mS ≤ ‖S (ellipse c a b s)‖)
    (hr : d * (π * τ * Real.exp (π * Y) + τ * Real.exp (π * Y) / mS * L) ≤ r) :
    ∀ μ : Measure ℝ, ClassA τ μ → ∀ s ∈ Icc s₀ s₁, ∀ lam ∈ Ioc (0 : ℝ) 1,
      S (ellipse c a b s) = lam * hat μ (ellipse c a b s) → ∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r := by
  intro μ hμ s hs lam hlam hcr
  obtain ⟨h1, h2⟩ := localization hτ hμ (hd s hs) hY hL hmS (hSz s hs) hlam hcr
  exact ⟨1 / lam, h1, h2.trans hr⟩

/-- The pinned values are bounded: `|μ̂(p)| ≤ τ e^{π |Im p|} ≤ R`. -/
theorem pinned_bound {τ : ℝ} (hτ : 0 ≤ τ) {μ : Measure ℝ} (hμ : ClassA τ μ) {p : ℂ} {R : ℝ}
    (hR : τ * Real.exp (π * |p.im|) ≤ R) : |(hat μ p).re| ≤ R ∧ |(hat μ p).im| ≤ R :=
  ⟨(Complex.abs_re_le_norm _).trans ((norm_hat_le hτ hμ p).trans hR),
    (Complex.abs_im_le_norm _).trans ((norm_hat_le hτ hμ p).trans hR)⟩

end C64
