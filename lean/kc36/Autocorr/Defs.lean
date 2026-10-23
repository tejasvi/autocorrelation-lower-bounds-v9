import Mathlib

/-!
# The discrete window functional and the discrete claims

For `p : Fin n → ℝ` (bin masses) and a window `0 ≤ c1 ≤ c2 ≤ 2n-2`,
`winSum p c1 c2 = Σ_{c1 ≤ i+j ≤ c2} p_i p_j` (ordered pairs), and the window value is
`q_{c1 c2}(p) = 2n/(c2-c1+2) · winSum p c1 c2`.  `F_n(p) = max_W q_W(p)`.

* `DiscreteClaim n lam`: every `p` in the simplex has a window with `q_W(p) ≥ lam`, i.e. `F_n(p) ≥ lam`.
* `HalfClaim n lam`: the same for `p` in the simplex with `Σ_i (2i-(n-1)) p_i ≤ 0`.

The inequality `lam ≤ 2n/(c2-c1+2) · winSum` is stated multiplied out (`WinOK`).
-/

open scoped BigOperators

namespace Autocorr

/-- `winSum p c1 c2 = Σ_{c1 ≤ i+j ≤ c2} p_i p_j` over ordered pairs `(i, j)`. -/
noncomputable def winSum {n : ℕ} (p : Fin n → ℝ) (c1 c2 : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if c1 ≤ (i : ℕ) + j ∧ (i : ℕ) + j ≤ c2 then p i * p j else 0

/-- The window `(c1, c2)` is admissible and certifies `lam` at `p`:
`0 ≤ c1 ≤ c2 ≤ 2n-2` and `lam · (c2-c1+2) ≤ 2n · winSum p c1 c2`. -/
def WinOK {n : ℕ} (lam : ℝ) (p : Fin n → ℝ) (c1 c2 : ℕ) : Prop :=
  c1 ≤ c2 ∧ c2 + 2 ≤ 2 * n ∧ lam * ((c2 : ℝ) - c1 + 2) ≤ 2 * n * winSum p c1 c2

/-- The discrete claim `D(n, lam)`: `F_n(p) ≥ lam` on the simplex. -/
def DiscreteClaim (n : ℕ) (lam : ℝ) : Prop :=
  ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → ∃ c1 c2, WinOK lam p c1 c2

/-- `D(n, lam)` on the half-space `Σ_i (2i-(n-1)) p_i ≤ 0`. -/
def HalfClaim (n : ℕ) (lam : ℝ) : Prop :=
  ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    ∑ i : Fin n, (2 * ((i : ℕ) : ℝ) - ((n : ℝ) - 1)) * p i ≤ 0 → ∃ c1 c2, WinOK lam p c1 c2

end Autocorr
