import AutocorrCert.Decode
import Autocorr.Cert.SoundMain
import Autocorr.Reduction

/-!
# From an accepted certificate string to the autoconvolution inequality

`checkWhole n lam s = true` (the whole DFS log in one segment, from the root box to the empty
stack) implies `HalfClaim n lam`, hence the inequality for every measurable `f : ℝ → ℝ≥0∞`.
The decoder is untrusted: the proof only uses the Boolean checks.
-/

open MeasureTheory ENNReal Set

namespace Autocorr.Cert

theorem checkSegStr_sound {n : ℕ} {lam : ℚ} {stkIn stkOut : List Box} {s : String}
    (h : checkSegStr n lam stkIn stkOut s = true) :
    StackOK (mkSpec n) lam stkOut → StackOK (mkSpec n) lam stkIn := by
  simp only [checkSegStr, Bool.and_eq_true] at h
  exact checkSeg_sound h.2

theorem checkSegStr_wf {n : ℕ} {lam : ℚ} {stkIn stkOut : List Box} {s : String}
    (h : checkSegStr n lam stkIn stkOut s = true) : (mkSpec n).wf = true := by
  simp only [checkSegStr, checkSeg, Bool.and_eq_true] at h
  exact h.2.1.1

theorem halfClaim_of_checkWhole {n : ℕ} {lam : ℚ} {s : String} (h : checkWhole n lam s = true) :
    HalfClaim n (lam : ℝ) := by
  unfold checkWhole at h
  split at h
  · rename_i R hR
    have hwf := checkSegStr_wf h
    have hR' : StackOK (mkSpec n) lam [R] := checkSegStr_sound h (by simp [StackOK])
    exact halfClaim_of_rootOK hwf hR (hR' R (List.mem_singleton_self R))
  · exact absurd h (by simp)

end Autocorr.Cert
