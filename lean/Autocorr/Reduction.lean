import Autocorr.Analytic
import Autocorr.Reversal

/-!
# From the discrete claim to the autoconvolution inequality

`autocorr_lower_of_claim`: if `D(n, lam)` holds then for every measurable `f : ℝ → ℝ≥0∞`

  `lam · (∫⁻_{[-1/4,1/4]} f)² ≤ sup_{t ∈ [-1/2,1/2]} ∫⁻ f(t-x) f(x) dx`.

Cases: if the supremum is `∞` there is nothing to prove; otherwise every bin mass is finite
(an infinite `p_i` and the window `(2i, 2i)` would force the supremum to be `∞`); if all masses
vanish the left side is `0`; else normalise and apply `D(n, lam)` (homogeneity of degree 2).
-/

open MeasureTheory ENNReal Set
open scoped BigOperators

namespace Autocorr

/-- The reduction for any `S` that bounds the window sums as in the window lemma. -/
theorem lower_of_windows {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hD : DiscreteClaim n lam) (f : ℝ → ℝ≥0∞) (hf : Measurable f) (S : ℝ≥0∞)
    (hW0 : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * n →
      ∑ ij ∈ winPairs n c1 c2, (∫⁻ x in bin n ij.1, f x) * (∫⁻ x in bin n ij.2, f x) ≤
        ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * S) :
    ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤ S := by
  set A := ∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x with hA
  set p : Fin n → ℝ≥0∞ := fun i => ∫⁻ x in bin n i, f x with hp
  have hAp : A ≤ ∑ i, p i := lintegral_Icc_le_sum_bins hn f hf
  have hW : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * n →
      ∑ ij ∈ winPairs n c1 c2, p ij.1 * p ij.2 ≤
        ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * S := hW0
  clear_value A p
  by_cases hStop : S = ⊤
  · rw [hStop]; exact le_top
  -- every bin mass is finite
  have hfin : ∀ i, p i ≠ ⊤ := by
    intro i hi
    have hmem : (i, i) ∈ winPairs n (2 * i) (2 * i) := by
      simp only [winPairs, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h1 : p i * p i ≤ ∑ ij ∈ winPairs n (2 * i) (2 * i), p ij.1 * p ij.2 :=
      Finset.single_le_sum (f := fun ij : Fin n × Fin n => p ij.1 * p ij.2)
        (fun _ _ => zero_le) hmem
    have h2 := hW (2 * i) (2 * i) le_rfl (by omega)
    have htop : p i * p i = ⊤ := by rw [hi]; simp
    rw [htop] at h1
    have h3 := top_le_iff.mp (h1.trans h2)
    rw [ENNReal.mul_eq_top] at h3
    rcases h3 with ⟨_, h⟩ | ⟨h, _⟩
    · exact hStop h
    · exact ENNReal.ofReal_ne_top h
  set q : Fin n → ℝ := fun i => (p i).toReal with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => ENNReal.toReal_nonneg
  have hpq : ∀ i, p i = ENNReal.ofReal (q i) := fun i => (ENNReal.ofReal_toReal (hfin i)).symm
  set Q := ∑ i, q i with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => hq0 i)
  have hsumpQ : ∑ i, p i = ENNReal.ofReal Q := by
    rw [hQ, ENNReal.ofReal_sum_of_nonneg (fun i _ => hq0 i)]
    exact Finset.sum_congr rfl (fun i _ => hpq i)
  by_cases hQz : Q = 0
  · have hA0 : A = 0 := by
      have : A ≤ 0 := by
        have h := hAp
        rw [hsumpQ, hQz, ENNReal.ofReal_zero] at h
        exact h
      exact le_antisymm this zero_le
    rw [hA0]; simp
  have hQpos : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQz)
  set r : Fin n → ℝ := fun i => q i / Q with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => div_nonneg (hq0 i) hQ0
  have hr1 : ∑ i, r i = 1 := by
    rw [hr, ← Finset.sum_div, ← hQ, div_self hQz]
  obtain ⟨c1, c2, h12, h2, hineq⟩ := hD r hr0 hr1
  have hwr : winSum r c1 c2 = winSum q c1 c2 / Q ^ 2 := by
    rw [winSum_eq_sum_winPairs, winSum_eq_sum_winPairs, Finset.sum_div]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    simp only [hr]
    field_simp
  have hwq : ∑ ij ∈ winPairs n c1 c2, p ij.1 * p ij.2 = ENNReal.ofReal (winSum q c1 c2) := by
    rw [winSum_eq_sum_winPairs,
      ENNReal.ofReal_sum_of_nonneg (fun ij _ => mul_nonneg (hq0 _) (hq0 _))]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [ENNReal.ofReal_mul (hq0 _), ← hpq, ← hpq]
  have hc12 : (c1 : ℝ) ≤ c2 := by exact_mod_cast h12
  have hkpos : 0 < (c2 : ℝ) - c1 + 2 := by linarith
  have hnpos : (0 : ℝ) < 2 * n := by positivity
  have hwq0 : 0 ≤ winSum q c1 c2 := by
    rw [winSum_eq_sum_winPairs]
    exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hq0 _) (hq0 _))
  have hreal : lam * Q ^ 2 ≤ (2 * n / ((c2 : ℝ) - c1 + 2)) * winSum q c1 c2 := by
    rw [hwr] at hineq
    have hQ2 : 0 < Q ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
    have h' : lam * ((c2 : ℝ) - c1 + 2) * Q ^ 2 ≤ 2 * n * winSum q c1 c2 := by
      have := mul_le_mul_of_nonneg_right hineq hQ2.le
      rwa [mul_assoc (2 * (n : ℝ)), div_mul_cancel₀ _ hQ2.ne'] at this
    linarith
  calc ENNReal.ofReal lam * A ^ 2 ≤ ENNReal.ofReal lam * (ENNReal.ofReal Q) ^ 2 := by
        gcongr
        rw [← hsumpQ]; exact hAp
    _ = ENNReal.ofReal (lam * Q ^ 2) := by
        rw [ENNReal.ofReal_mul hlam, ENNReal.ofReal_pow hQ0]
    _ ≤ ENNReal.ofReal ((2 * n / ((c2 : ℝ) - c1 + 2)) * winSum q c1 c2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * n / ((c2 : ℝ) - c1 + 2)) *
          ∑ ij ∈ winPairs n c1 c2, p ij.1 * p ij.2 := by
        rw [hwq, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (2 * n / ((c2 : ℝ) - c1 + 2)) *
          (ENNReal.ofReal (((c2 : ℝ) - c1 + 2) / (2 * n)) * S) := by
        gcongr
        exact hW c1 c2 h12 h2
    _ = S := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show 2 * (n : ℝ) / ((c2 : ℝ) - c1 + 2) * (((c2 : ℝ) - c1 + 2) / (2 * n)) = 1 by
          field_simp]
        simp

theorem autocorr_lower_of_claim {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hD : DiscreteClaim n lam) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x :=
  lower_of_windows hn hlam hD f hf _ (fun _ _ h12 h2 => window_bound hn f hf h12 h2)

/-- The same bound with the ESSENTIAL supremum of `f ⋆ f` on `[-1/2, 1/2]` (`‖f ⋆ f‖_{L^∞(-1/2,1/2)}`),
which is at most the pointwise supremum (`essSup_conv_le_iSup`). -/
theorem autocorr_lower_ess_of_claim {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hD : DiscreteClaim n lam) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) :=
  lower_of_windows hn hlam hD f hf _ (fun _ _ _ h2 => window_bound_ae hn f hf h2 ae_le_essSup)

lemma essSup_conv_le_iSup (f : ℝ → ℝ≥0∞) :
    essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x :=
  essSup_le_of_ae_le _ (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht =>
    le_iSup₂ (f := fun t (_ : t ∈ Icc (-1/2 : ℝ) (1/2)) => ∫⁻ x, f (t - x) * f x) t ht))

/-- The half-space claim suffices (reversal symmetry). -/
theorem autocorr_lower_of_halfClaim {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : HalfClaim n lam) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      ⨆ t ∈ Icc (-1/2 : ℝ) (1/2), ∫⁻ x, f (t - x) * f x :=
  autocorr_lower_of_claim hn hlam (discreteClaim_of_halfClaim hH) f hf

theorem autocorr_lower_ess_of_halfClaim {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : HalfClaim n lam) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal lam * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) :=
  autocorr_lower_ess_of_claim hn hlam (discreteClaim_of_halfClaim hH) f hf

end Autocorr
