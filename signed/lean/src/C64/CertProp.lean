import C64.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The certificate layer (Section 6 of the paper), in winding-number form

The paper counts zeros inside Jordan curves with the argument principle.  The Lean proof uses winding
numbers of loops in `ℂ \ {0}` instead, which needs neither the argument principle nor the Jordan curve
theorem:

* `F² = M · G_w` on the curve gives `wind(G_w ∘ T) = 2 · wind(F ∘ T)`, an even number;
* the homotopies of Lemmas 6.2 and 6.4 keep the winding number constant (homotopy lifting through
  `exp`, Mathlib's `Complex.isCoveringMap_exp` and `IsCoveringMap.liftHomotopy`);
* the winding numbers of `S` along `T₁` and of `G_{ν_rep}` along a tile are computed by the
  checker from a subdivision whose pieces map into open half-planes.

`HasWinding g n` says that `g` has a continuous logarithm on `[0, 1]` whose total change is `2πi n`.
-/

open MeasureTheory Set Complex Real

namespace C64

/-- `K_t(z) = exp(-2πitz)`. -/
noncomputable def Kt (t : ℝ) (z : ℂ) : ℂ := Complex.exp (-2 * π * I * t * z)

/-- `S(z) = sin(πz)/(πz)`, `S(0) = 1`. -/
noncomputable def S (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin (π * z) / (π * z)

/-- The Fourier–Laplace transform `μ̂(z) = ∫ K_t(z) dμ(t)` of a measure on `ℝ`. -/
noncomputable def hat (μ : Measure ℝ) (z : ℂ) : ℂ := ∫ t, Kt t z ∂μ

/-- `G_μ = S - μ̂`. -/
noncomputable def G (μ : Measure ℝ) (z : ℂ) : ℂ := S z - hat μ z

/-- The class `𝒜_τ` of the one-sided case: nonnegative measures on `[-1/2, 1/2]` of mass at most `τ`. -/
def ClassA (τ : ℝ) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧ μ (Icc (-1/2 : ℝ) (1/2))ᶜ = 0 ∧ μ univ ≤ ENNReal.ofReal τ

/-- The ellipse `z(s) = c + a cos 2πs + i b sin 2πs` (`c` complex: the tiles have complex centres). -/
noncomputable def ellipse (c : ℂ) (a b : ℝ) (s : ℝ) : ℂ :=
  c + (a * Real.cos (2 * π * s) : ℝ) + ((b * Real.sin (2 * π * s) : ℝ) : ℂ) * I

/-- `g` has winding number `n` along `[0, 1]`: a continuous logarithm of `g` on `[0, 1]` changes by
`2πi n`. -/
def HasWinding (g : ℝ → ℂ) (n : ℤ) : Prop :=
  ∃ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) ∧ (∀ s ∈ Icc (0 : ℝ) 1, Complex.exp (L s) = g s) ∧
    L 1 - L 0 = 2 * π * I * n

/-- `G_μ` has an odd-winding ellipse: it does not vanish on some ellipse and winds an odd number of
times around `0` along it.  (In the paper: `G_μ` has an odd number of zeros inside a tile.) -/
def OddLoop (μ : Measure ℝ) : Prop :=
  ∃ (c : ℂ) (a b : ℝ), 0 < a ∧ 0 < b ∧ (∀ s ∈ Icc (0 : ℝ) 1, G μ (ellipse c a b s) ≠ 0) ∧
    ∃ n : ℤ, Odd n ∧ HasWinding (fun s => G μ (ellipse c a b s)) n

/-- The arc `z([s₀, s₁])` of `T₁` is settled at level `τ`: every measure of `𝒜_τ` with a crossing on it
(`S(z) = λ μ̂(z)` with `λ ∈ (0, 1]`) has an odd-winding ellipse.  Type E arcs are settled because no
crossing exists there; type H and H3 arcs by Lemmas 6.3–6.5 and a witness. -/
def ArcSettled (τ : ℝ) (c a b s₀ s₁ : ℝ) : Prop :=
  ∀ μ : Measure ℝ, ClassA τ μ → ∀ s ∈ Icc s₀ s₁, ∀ lam ∈ Ioc (0 : ℝ) 1,
    S (ellipse c a b s) = lam * hat μ (ellipse c a b s) → OddLoop μ

/-- Consecutive arcs `[s₀,s₁], [s₁,s₂], …` from `0` to `1`. -/
def CoversUnit : List (ℝ × ℝ) → Prop
  | [] => False
  | [p] => p.2 = 1
  | p :: q :: rest => p.2 = q.1 ∧ CoversUnit (q :: rest)

/-- Proposition 6.7 + Corollary 6.8 (one-sided case) in arc form: if `S` winds an odd number of times
along `T₁` and settled arcs cover `[0, 1]`, then every admissible `f` with `∫ f ≠ 0` has
`ess sup (f ⋆ f) > (∫ f)² / (1 - τ)`.  To be proved in full (no hypotheses). -/
def ArcReduction : Prop :=
  ∀ (τ c a b : ℝ), 0 < τ → τ < 1 → 0 < a → 0 < b →
    (∀ s ∈ Icc (0 : ℝ) 1, S (ellipse c a b s) ≠ 0) →
    (∃ n : ℤ, Odd n ∧ HasWinding (fun s => S (ellipse c a b s)) n) →
    ∀ arcs : List (ℝ × ℝ), (∀ p ∈ arcs.head?, p.1 = 0) → CoversUnit arcs →
    (∀ p ∈ arcs, ArcSettled τ c a b p.1 p.2) →
    ∀ f : ℝ → ℝ, Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
      (∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ M) → (∫ x, f x) ^ 2 / (1 - τ) < M

end C64
