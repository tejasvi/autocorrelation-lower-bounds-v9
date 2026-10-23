import Autocorr.Defs

/-!
# Reversal symmetry

`p_i ↦ p_{n-1-i}` maps the window `(c1, c2)` to `(2n-2-c2, 2n-2-c1)` and flips the sign of
`Σ_i (2i-(n-1)) p_i`, so the half-space claim implies the full discrete claim.
-/

open scoped BigOperators

namespace Autocorr

variable {n : ℕ}

lemma winSum_rev (p : Fin n → ℝ) {c1 c2 : ℕ} (h12 : c1 ≤ c2) (h2 : c2 + 2 ≤ 2 * n) :
    winSum (fun i => p (Fin.rev i)) c1 c2 = winSum p (2 * n - 2 - c2) (2 * n - 2 - c1) := by
  unfold winSum
  rw [← Equiv.sum_comp (Fin.revPerm (n := n))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp (Fin.revPerm (n := n))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : (c1 ≤ n - (i + 1) + (n - (j + 1)) ∧ n - (i + 1) + (n - (j + 1)) ≤ c2) ↔
      (2 * n - 2 - c2 ≤ (i : ℕ) + j ∧ (i : ℕ) + j ≤ 2 * n - 2 - c1) := by
    omega
  by_cases h : c1 ≤ n - (i + 1) + (n - (j + 1)) ∧ n - (i + 1) + (n - (j + 1)) ≤ c2
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem discreteClaim_of_halfClaim {lam : ℝ} (hD : HalfClaim n lam) : DiscreteClaim n lam := by
  intro p hp hsum
  by_cases hh : ∑ i : Fin n, (2 * ((i : ℕ) : ℝ) - ((n : ℝ) - 1)) * p i ≤ 0
  · exact hD p hp hsum hh
  · set p' : Fin n → ℝ := fun i => p (Fin.rev i) with hp'def
    have hp' : ∀ i, 0 ≤ p' i := fun i => hp _
    have hsum' : ∑ i, p' i = 1 := by
      rw [hp'def, ← hsum]
      exact Equiv.sum_comp (Fin.revPerm (n := n)) p
    have hh' : ∑ i : Fin n, (2 * ((i : ℕ) : ℝ) - ((n : ℝ) - 1)) * p' i ≤ 0 := by
      have key : ∑ i : Fin n, (2 * ((i : ℕ) : ℝ) - ((n : ℝ) - 1)) * p' i =
          -∑ i : Fin n, (2 * ((i : ℕ) : ℝ) - ((n : ℝ) - 1)) * p i := by
        rw [← Finset.sum_neg_distrib, hp'def]
        rw [← Equiv.sum_comp (Fin.revPerm (n := n))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
        have hi := i.isLt
        have : ((n - (i + 1) : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; ring
      rw [key]; linarith
    obtain ⟨c1, c2, h12, h2, hineq⟩ := hD p' hp' hsum' hh'
    refine ⟨2 * n - 2 - c2, 2 * n - 2 - c1, by omega, by omega, ?_⟩
    rw [← winSum_rev p h12 h2]
    have hc : ((2 * n - 2 - c1 : ℕ) : ℝ) - ((2 * n - 2 - c2 : ℕ) : ℝ) = (c2 : ℝ) - c1 := by
      have e1 : (2 * n - 2 - c1 : ℕ) + c1 + 2 = 2 * n := by omega
      have e2 : (2 * n - 2 - c2 : ℕ) + c2 + 2 = 2 * n := by omega
      have f1 := congrArg (Nat.cast : ℕ → ℝ) e1
      have f2 := congrArg (Nat.cast : ℕ → ℝ) e2
      push_cast at f1 f2
      linarith
    rw [hc]
    exact hineq

end Autocorr
