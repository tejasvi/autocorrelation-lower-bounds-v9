import C64.Settle

/-!
# Finite atomic measures (the representative measures `w_rep` of the witnesses)

`atomic ts ms = Σ_i m_i δ_{t_i}`; `hat_atomic`: `μ̂(z) = Σ_i m_i K_{t_i}(z)`; `classA_atomic`: it lies in `𝒜_τ`
when the masses are nonnegative with sum at most `τ` and the atoms lie in `[-1/2, 1/2]`.
-/

open MeasureTheory Set Complex Real

namespace C64

/-- `Σ_i m_i δ_{t_i}`. -/
noncomputable def atomic {N : ℕ} (ts ms : Fin N → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (ms i) • Measure.dirac (ts i)

instance {N : ℕ} (ts ms : Fin N → ℝ) : IsFiniteMeasure (atomic ts ms) := ⟨by
  rw [atomic, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 (fun i _ => ENNReal.ofReal_lt_top)⟩

theorem hat_atomic {N : ℕ} (ts ms : Fin N → ℝ) (hm : ∀ i, 0 ≤ ms i) (z : ℂ) :
    hat (atomic ts ms) z = ∑ i, (ms i : ℂ) * Kt (ts i) z := by
  rw [hat, atomic, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hm i), Complex.real_smul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem classA_atomic {N : ℕ} (ts ms : Fin N → ℝ) (hm : ∀ i, 0 ≤ ms i) {τ : ℝ}
    (hsum : ∑ i, ms i ≤ τ) (ht : ∀ i, ts i ∈ Icc (-1/2 : ℝ) (1/2)) : ClassA τ (atomic ts ms) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [atomic, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl, indicator_of_notMem (by simpa using ht i), mul_zero]
  · rw [atomic, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hm i)]
    exact ENNReal.ofReal_le_ofReal hsum

end C64
