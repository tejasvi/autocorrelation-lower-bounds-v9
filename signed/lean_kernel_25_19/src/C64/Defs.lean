import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Data.EReal.Basic

/-!
# Problem 6.4 (signed autoconvolution constants): statement

For an integrable `f : ℝ → ℝ` that vanishes almost everywhere outside `[-1/4, 1/4]`, `C₃` and `C₃'` are
the largest constants with

  `ess sup_t |(f ⋆ f)(t)| ≥ C₃ (∫ f)²`   and   `ess sup_t (f ⋆ f)(t) ≥ C₃' (∫ f)²`.

`f ⋆ f` is Mathlib's convolution with real multiplication, `(f ⋆ f)(t) = ∫ f(s) f(t - s) ds`.  For
integrable `f` this integral converges for almost every `t`, and the essential supremum ignores the
other points.  An essential supremum bound is written with real almost-everywhere upper bounds `M`;
the `EReal` essential supremum appears in `MainStatement`.
-/

open MeasureTheory Set

namespace C64

/-- The autoconvolution `(f ⋆ f)(t) = ∫ f(s) f(t - s) ds`. -/
noncomputable def autoconv (f : ℝ → ℝ) : ℝ → ℝ :=
  convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume

/-- The class of Problem 6.4: integrable and zero almost everywhere outside `[-1/4, 1/4]`. -/
def Admissible (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ ∀ᵐ x ∂(volume : Measure ℝ), x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0

/-- `C` is a valid constant for `C₃'`: every real a.e. upper bound `M` of `f ⋆ f` is at least
`C (∫ f)²`, for every admissible `f`. -/
def ValidC3' (C : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → ∀ M : ℝ,
    (∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ M) → C * (∫ x, f x) ^ 2 ≤ M

/-- `C` is a valid constant for `C₃` (the same with `|f ⋆ f|`). -/
def ValidC3 (C : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → ∀ M : ℝ,
    (∀ᵐ t ∂(volume : Measure ℝ), |autoconv f t| ≤ M) → C * (∫ x, f x) ^ 2 ≤ M

/-- `C₃'`, the supremum of the valid constants (in `EReal`, so no boundedness condition is needed). -/
noncomputable def C3' : EReal := sSup ((fun C : ℝ => (C : EReal)) '' {C | ValidC3' C})

/-- `C₃`, the supremum of the valid constants for `|f ⋆ f|`. -/
noncomputable def C3 : EReal := sSup ((fun C : ℝ => (C : EReal)) '' {C | ValidC3 C})

/-- The main theorem of the paper (one-sided form, strict): for admissible `f` with `∫ f ≠ 0`, every real
a.e. upper bound of `f ⋆ f` exceeds `(25/19) (∫ f)²`. -/
def MainStatement : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
    (∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ M) → (25/19 : ℝ) * (∫ x, f x) ^ 2 < M

/-- The same with the essential suprema in `EReal`:
`ess sup |f ⋆ f| ≥ ess sup (f ⋆ f) > (25/19) (∫ f)²`. -/
def MainStatementEss : Prop :=
  ∀ f : ℝ → ℝ, Admissible f → ∫ x, f x ≠ 0 →
    (((25/19 : ℝ) * (∫ x, f x) ^ 2 : ℝ) : EReal) <
        essSup (fun t => ((autoconv f t : ℝ) : EReal)) volume ∧
      essSup (fun t => ((autoconv f t : ℝ) : EReal)) volume ≤
        essSup (fun t => ((|autoconv f t| : ℝ) : EReal)) volume

/-- The headline: `C₃ ≥ C₃' ≥ 25/19`. -/
def ConstStatement : Prop := ((25/19 : ℝ) : EReal) ≤ C3' ∧ C3' ≤ C3

end C64
