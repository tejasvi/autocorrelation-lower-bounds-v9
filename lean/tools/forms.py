"""Write Autocorr/<PKG>/Forms.lean: the essential-supremum and real-valued forms of a certificate's bound,
derived from its `halfClaim` and `ofReal_lam` (works for the M3 and the M4 packages).
usage: forms.py PKG N A B [--root DIR]"""
import os, sys, argparse

ap = argparse.ArgumentParser()
ap.add_argument("pkg"); ap.add_argument("n", type=int); ap.add_argument("a", type=int); ap.add_argument("b", type=int)
ap.add_argument("--root", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
args = ap.parse_args()
pkg, n, a, b = args.pkg, args.n, args.a, args.b
src = f"""import Autocorr.{pkg}.Main
import Autocorr.RealForm

/-! Further forms of the bound `C₁ ≥ {a}/{b}` proved in `Autocorr.{pkg}.Main`. -/

open MeasureTheory ENNReal Set

namespace Autocorr.{pkg}

/-- Essential-supremum form: for every measurable `f : ℝ → [0, ∞]`,
`{a}/{b} · (∫_{{-1/4}}^{{1/4}} f)² ≤ ‖f ⋆ f‖_{{L^∞(-1/2, 1/2)}}` (`essSup`; at most the pointwise supremum). -/
theorem autocorr_lower_ess (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ({a} / {b} : ℝ≥0∞) * (∫⁻ x in Icc (-1/4 : ℝ) (1/4), f x) ^ 2 ≤
      essSup (fun t => ∫⁻ x, f (t - x) * f x) (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  rw [← ofReal_lam]
  exact autocorr_lower_ess_of_halfClaim (by norm_num) (by positivity) halfClaim f hf

/-- Real-valued form with Mathlib's convolution: for `f : ℝ → ℝ` measurable, nonnegative and vanishing outside
`[-1/4, 1/4]`, `{a}/{b} · (∫ f)² ≤ ‖f ⋆ f‖_{{L^∞(-1/2, 1/2)}}` (the norm in `ℝ≥0∞`). -/
theorem autocorr_lower_real (f : ℝ → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : ∀ x, x ∉ Icc (-1/4 : ℝ) (1/4) → f x = 0) :
    ENNReal.ofReal ({a} / {b} * (∫ x, f x) ^ 2) ≤
      eLpNorm (convolution f f (ContinuousLinearMap.mul ℝ ℝ) volume) ⊤
        (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
  have h := autocorr_lower_real_of_halfClaim (by norm_num) (by positivity) halfClaim f hf hf0 hsupp
  convert h using 3 <;> norm_num

end Autocorr.{pkg}
"""
fn = os.path.join(args.root, "Autocorr", pkg, "Forms.lean")
if not os.path.exists(fn) or open(fn).read() != src:
    open(fn, "w").write(src)
print(fn)
