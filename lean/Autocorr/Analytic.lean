import Autocorr.Defs

/-!
# The analytic reduction (Cloninger–Steinerberger window lemma)

For measurable `f : ℝ → ℝ≥0∞` let `p_i = ∫⁻_{B_i} f` with the bins
`B_i = [-1/4 + i/(2n), -1/4 + (i+1)/(2n))`, `i < n`.  For a window `0 ≤ c1 ≤ c2 ≤ 2n-2` and
`J = [-1/2 + c1/(2n), -1/2 + (c2+2)/(2n)] ⊆ [-1/2, 1/2]`, the sets `B_i + B_j` with
`c1 ≤ i+j ≤ c2` lie in `J`, so by Tonelli

  `Σ_{c1 ≤ i+j ≤ c2} p_i p_j ≤ ∫⁻_J (f ⋆ f) ≤ |J| · sup_{[-1/2,1/2]} (f ⋆ f)`.

No truncation of `f` is needed: the bins only see `f` on `[-1/4, 1/4)`.  The discrete claim
then gives the bound by homogeneity.  Infinite masses are handled separately (an infinite `p_i`
forces the supremum to be `∞`).
-/

open MeasureTheory ENNReal Set
open scoped BigOperators

namespace Autocorr

variable {n : ℕ}

/-- The autoconvolution of `f` at `t`. -/
noncomputable def conv (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := ∫⁻ x, f (t - x) * f x

/-- Bin `i`: `[-1/4 + i/(2n), -1/4 + (i+1)/(2n))`. -/
def bin (n i : ℕ) : Set ℝ := Ico (-1/4 + (i : ℝ) / (2 * n)) (-1/4 + ((i : ℝ) + 1) / (2 * n))

/-- The window interval `[-1/2 + c1/(2n), -1/2 + (c2+2)/(2n)]`. -/
def winSet (n c1 c2 : ℕ) : Set ℝ :=
  Icc (-1/2 + (c1 : ℝ) / (2 * n)) (-1/2 + ((c2 : ℝ) + 2) / (2 * n))

lemma bin_eq_empty_or_disjoint (hn : 0 < n) {i j : ℕ} (hij : i ≠ j) {x : ℝ}
    (hi : x ∈ bin n i) : x ∉ bin n j := by
  intro hj
  simp only [bin, mem_Ico] at hi hj
  have hpos : (0 : ℝ) < 2 * n := by positivity
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · -- i < j: x < -1/4 + (i+1)/(2n) ≤ -1/4 + j/(2n) ≤ x
    have : ((i : ℝ) + 1) / (2 * n) ≤ (j : ℝ) / (2 * n) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      exact_mod_cast h
    linarith [hi.2, hj.1]
  · have : ((j : ℝ) + 1) / (2 * n) ≤ (i : ℝ) / (2 * n) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      exact_mod_cast h
    linarith [hj.2, hi.1]

lemma add_mem_winSet (hn : 0 < n) {i j c1 c2 : ℕ} (h1 : c1 ≤ i + j) (h2 : i + j ≤ c2) {x y : ℝ}
    (hx : x ∈ bin n i) (hy : y ∈ bin n j) : y + x ∈ winSet n c1 c2 := by
  simp only [bin, mem_Ico] at hx hy
  simp only [winSet, mem_Icc]
  have hpos : (0 : ℝ) < 2 * n := by positivity
  have h1' : (c1 : ℝ) ≤ i + j := by exact_mod_cast h1
  have h2' : (i : ℝ) + j ≤ c2 := by exact_mod_cast h2
  constructor
  · have : (c1 : ℝ) / (2 * n) ≤ (i : ℝ) / (2 * n) + (j : ℝ) / (2 * n) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right h1' hpos.le
    linarith [hx.1, hy.1]
  · have : ((i : ℝ) + 1) / (2 * n) + ((j : ℝ) + 1) / (2 * n) ≤ ((c2 : ℝ) + 2) / (2 * n) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hpos.le
    linarith [hx.2, hy.2]

lemma winSet_subset (hn : 0 < n) {c1 c2 : ℕ} (h2 : c2 + 2 ≤ 2 * n) :
    winSet n c1 c2 ⊆ Icc (-1/2 : ℝ) (1/2) := by
  intro t ht
  simp only [winSet, mem_Icc] at ht ⊢
  have hpos : (0 : ℝ) < 2 * n := by positivity
  have h0 : (0 : ℝ) ≤ (c1 : ℝ) / (2 * n) := by positivity
  have h1 : ((c2 : ℝ) + 2) / (2 * n) ≤ 1 := by
    rw [div_le_one hpos]; exact_mod_cast h2
  constructor <;> linarith [ht.1, ht.2]

lemma volume_winSet {c1 c2 : ℕ} :
    volume (winSet n c1 c2) = ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) := by
  rw [winSet, Real.volume_Icc]
  congr 1
  ring

/-- The window index set `{(i, j) : c1 ≤ i + j ≤ c2}` (ordered pairs). -/
def winPairs (n c1 c2 : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => c1 ≤ (ij.1 : ℕ) + ij.2 ∧ (ij.1 : ℕ) + ij.2 ≤ c2)

lemma winSum_eq_sum_winPairs (p : Fin n → ℝ) (c1 c2 : ℕ) :
    winSum p c1 c2 = ∑ ij ∈ winPairs n c1 c2, p ij.1 * p ij.2 := by
  rw [winPairs, Finset.sum_filter, Fintype.sum_prod_type]
  rfl

/-- Pointwise: products of bin indicators over a window are dominated by the window indicator. -/
lemma window_pointwise (hn : 0 < n) (f : ℝ → ℝ≥0∞) {c1 c2 : ℕ} (x y : ℝ) :
    (∑ ij ∈ winPairs n c1 c2, (bin n ij.1).indicator f x * (bin n ij.2).indicator f y)
      ≤ (winSet n c1 c2).indicator 1 (y + x) * (f y * f x) := by
  by_cases hex : ∃ ij ∈ winPairs n c1 c2, x ∈ bin n ij.1 ∧ y ∈ bin n ij.2
  · obtain ⟨ij, hij, hx, hy⟩ := hex
    have hc := (Finset.mem_filter.mp hij).2
    rw [Finset.sum_eq_single_of_mem ij hij]
    · rw [indicator_of_mem hx, indicator_of_mem hy,
        indicator_of_mem (add_mem_winSet hn hc.1 hc.2 hx hy)]
      simp [mul_comm]
    · intro kl _ hne
      by_cases h1 : kl.1 = ij.1
      · have h2 : kl.2 ≠ ij.2 := fun h2 => hne (Prod.ext h1 h2)
        have : y ∉ bin n kl.2 :=
          bin_eq_empty_or_disjoint hn (fun h => h2 (Fin.ext h).symm) hy
        simp [indicator_of_notMem this]
      · have : x ∉ bin n kl.1 :=
          bin_eq_empty_or_disjoint hn (fun h => h1 (Fin.ext h).symm) hx
        simp [indicator_of_notMem this]
  · push Not at hex
    rw [Finset.sum_eq_zero]
    · exact zero_le
    · intro ij hij
      by_cases hx : x ∈ bin n ij.1
      · simp [indicator_of_notMem (hex ij hij hx)]
      · simp [indicator_of_notMem hx]

/-- Tonelli part of the window lemma: `Σ_{c1 ≤ i+j ≤ c2} p_i p_j ≤ ∫⁻_J (f ⋆ f)`. -/
theorem window_sum_le_lintegral (hn : 0 < n) (f : ℝ → ℝ≥0∞) (hf : Measurable f) (c1 c2 : ℕ) :
    ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x) ≤
      ∫⁻ t in winSet n c1 c2, conv f t := by
  set J := winSet n c1 c2 with hJ
  have hJm : MeasurableSet J := measurableSet_Icc
  have hbm : ∀ i : ℕ, MeasurableSet (bin n i) := fun i => measurableSet_Ico
  -- ∫⁻_J conv as a double integral over (x, y)
  have hmeasG : Measurable (Function.uncurry fun (t x : ℝ) => J.indicator 1 t * (f (t - x) * f x)) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator hJm).comp measurable_fst
    · exact (hf.comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd)
  have step2 : ∫⁻ t in J, conv f t = ∫⁻ x, ∫⁻ y, J.indicator 1 (y + x) * (f y * f x) := by
    rw [← lintegral_indicator hJm]
    have e1 : ∀ t, J.indicator (conv f) t = ∫⁻ x, J.indicator 1 t * (f (t - x) * f x) := by
      intro t
      rw [lintegral_const_mul _ (by exact (hf.comp (measurable_const.sub measurable_id)).mul hf :
        Measurable fun x => f (t - x) * f x)]
      by_cases ht : t ∈ J
      · simp [indicator_of_mem ht, conv]
      · simp [indicator_of_notMem ht]
    simp_rw [e1]
    rw [lintegral_lintegral_swap hmeasG.aemeasurable]
    refine lintegral_congr (fun x => ?_)
    rw [← lintegral_add_right_eq_self (μ := volume)
      (fun t => J.indicator 1 t * (f (t - x) * f x)) x]
    simp only [add_sub_cancel_right]
  -- the window sum as a double integral
  have hFm : ∀ i : ℕ, Measurable ((bin n i).indicator f) := fun i => hf.indicator (hbm i)
  have step3 : ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x) =
      ∫⁻ x, ∫⁻ y, ∑ ij ∈ winPairs n c1 c2, (bin n ij.1).indicator f x * (bin n ij.2).indicator f y := by
    have inner : ∀ x, ∫⁻ y, ∑ ij ∈ winPairs n c1 c2, (bin n ij.1).indicator f x * (bin n ij.2).indicator f y
        = ∑ ij ∈ winPairs n c1 c2, ∫⁻ y, (bin n ij.1).indicator f x * (bin n ij.2).indicator f y := by
      intro x
      exact lintegral_finsetSum _ (fun ij _ => measurable_const.mul (hFm ij.2))
    simp_rw [inner]
    rw [lintegral_finsetSum]
    · refine Finset.sum_congr rfl (fun ij _ => ?_)
      rw [lintegral_lintegral_mul (hFm ij.1).aemeasurable (hFm ij.2).aemeasurable,
        lintegral_indicator (hbm ij.1), lintegral_indicator (hbm ij.2)]
    · intro ij _
      exact Measurable.lintegral_prod_right'
        (f := fun z : ℝ × ℝ => (bin n ij.1).indicator f z.1 * (bin n ij.2).indicator f z.2)
        (((hFm ij.1).comp measurable_fst).mul ((hFm ij.2).comp measurable_snd))
  calc ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x)
      = ∫⁻ x, ∫⁻ y, ∑ ij ∈ winPairs n c1 c2,
          (bin n ij.1).indicator f x * (bin n ij.2).indicator f y := step3
    _ ≤ ∫⁻ x, ∫⁻ y, J.indicator 1 (y + x) * (f y * f x) := by
        refine lintegral_mono (fun x => lintegral_mono (fun y => ?_))
        exact window_pointwise hn f x y
    _ = ∫⁻ t in J, conv f t := step2.symm

/-- The window lemma with any `S` bounding `f ⋆ f` almost everywhere on `[-1/2, 1/2]`:
`Σ_{c1 ≤ i+j ≤ c2} p_i p_j ≤ |J| · S`. -/
theorem window_bound_ae (hn : 0 < n) (f : ℝ → ℝ≥0∞) (hf : Measurable f) {c1 c2 : ℕ}
    (h2 : c2 + 2 ≤ 2 * n) {S : ℝ≥0∞}
    (hS : ∀ᵐ t ∂(volume.restrict (Icc (-1/2 : ℝ) (1/2))), conv f t ≤ S) :
    ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x) ≤
      ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * S := by
  refine (window_sum_le_lintegral hn f hf c1 c2).trans ?_
  calc ∫⁻ t in winSet n c1 c2, conv f t ≤ ∫⁻ _ in winSet n c1 c2, S :=
        lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset (winSet_subset hn h2) hS)
    _ = S * volume (winSet n c1 c2) := setLIntegral_const _ _
    _ = ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * S := by
        rw [volume_winSet, mul_comm]

/-- The window lemma: `Σ_{c1 ≤ i+j ≤ c2} p_i p_j ≤ |J| · sup_{[-1/2,1/2]} (f ⋆ f)`. -/
theorem window_bound (hn : 0 < n) (f : ℝ → ℝ≥0∞) (hf : Measurable f) {c1 c2 : ℕ}
    (_h12 : c1 ≤ c2) (h2 : c2 + 2 ≤ 2 * n) :
    ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x) ≤
      ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), conv f t :=
  window_bound_ae hn f hf h2 (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht =>
    le_iSup₂ (f := fun t (_ : t ∈ Icc (-1/2 : ℝ) (1/2)) => conv f t) t ht))

/-- The bins cover `[-1/4, 1/4]` up to a null set. -/
theorem lintegral_Icc_le_sum_bins (hn : 0 < n) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x ≤ ∑ i : Fin n, ∫⁻ x in bin n i, f x := by
  rw [← setLIntegral_congr (Ico_ae_eq_Icc (a := (-1/4 : ℝ)) (b := 1/4)),
    ← lintegral_indicator measurableSet_Ico]
  have hbm : ∀ i : ℕ, MeasurableSet (bin n i) := fun i => measurableSet_Ico
  simp_rw [← lintegral_indicator (hbm _)]
  rw [← lintegral_finsetSum (f := fun (i : Fin n) => (bin n i).indicator f) _
    (fun i _ => hf.indicator (hbm i))]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : x ∈ Ico (-1/4 : ℝ) (1/4)
  · rw [indicator_of_mem hx]
    simp only [mem_Ico] at hx
    have hpos : (0 : ℝ) < 2 * n := by positivity
    set k := ⌊(x + 1/4) * (2 * n)⌋₊ with hk
    have h0 : 0 ≤ (x + 1/4) * (2 * n) := by nlinarith
    have hk1 : (k : ℝ) ≤ (x + 1/4) * (2 * n) := Nat.floor_le h0
    have hk2 : (x + 1/4) * (2 * n) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hkn : k < n := by
      have : (k : ℝ) < n := by nlinarith
      exact_mod_cast this
    have hxk : x ∈ bin n k := by
      simp only [bin, mem_Ico]
      constructor
      · have : (k : ℝ) / (2 * n) ≤ x + 1/4 := by rw [div_le_iff₀ hpos]; linarith
        linarith
      · have : x + 1/4 < ((k : ℝ) + 1) / (2 * n) := by rw [lt_div_iff₀ hpos]; linarith
        linarith
    calc f x = (bin n (⟨k, hkn⟩ : Fin n)).indicator f x := by rw [indicator_of_mem hxk]
      _ ≤ ∑ i : Fin n, (bin n i).indicator f x :=
          Finset.single_le_sum (f := fun i : Fin n => (bin n i).indicator f x)
            (fun i _ => zero_le) (Finset.mem_univ _)
  · rw [indicator_of_notMem hx]
    exact zero_le

end Autocorr
