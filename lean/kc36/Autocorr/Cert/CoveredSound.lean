import AutocorrCert.Decode
import Autocorr.Cert.SoundMain
import Autocorr.Reduction

/-!
# Soundness of job composition

`Covered n lam s` (built in core Lean from accepted jobs) implies that every admissible point in
the region of the node at path `s` is good; for the root path this is `HalfClaim n lam`.
-/

namespace Autocorr.Cert

theorem covered_sound {n : ℕ} {lam : ℚ} {s : String} (h : Covered n lam s) :
    ∀ bx ∈ (regionOfPath (mkSpec n) (Dec.decodePath s)).toList, BoxOK (mkSpec n) lam bx := by
  induction h with
  | mk root children recs hchk hc ih =>
    unfold checkJobStr checkJob at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hwf, hlam⟩, hrun⟩ := hchk
    intro bx hbx
    rw [Option.mem_toList] at hbx
    rw [hbx] at hrun
    simp only [decide_eq_true_eq] at hrun
    have hst : StackOK (mkSpec n) lam
        ((children.map Dec.decodePath).filterMap (regionOfPath (mkSpec n))) := by
      intro b hb
      rw [List.mem_filterMap] at hb
      obtain ⟨path, hpath, hreg⟩ := hb
      rw [List.mem_map] at hpath
      obtain ⟨c, hc', rfl⟩ := hpath
      exact ih c hc' b (by rw [Option.mem_toList]; exact hreg)
    exact run_sound hwf hlam (Dec.decodeRecs recs) [bx] _ hrun hst bx (List.mem_singleton_self _)

theorem covered_wf {n : ℕ} {lam : ℚ} {s : String} (h : Covered n lam s) : (mkSpec n).wf = true := by
  cases h with
  | mk root children recs hchk hc =>
    unfold checkJobStr checkJob at hchk
    simp only [Bool.and_eq_true] at hchk
    exact hchk.1.1

/-- The root job covers the whole half-space. -/
theorem halfClaim_of_covered {n : ℕ} {lam : ℚ} (h : Covered n lam "")
    (hR : (rootBox (mkSpec n)).isSome = true) : HalfClaim n (lam : ℝ) := by
  obtain ⟨R, hR'⟩ := Option.isSome_iff_exists.mp hR
  have hs := covered_sound h
  have hpath : Dec.decodePath "" = [] := rfl
  rw [hpath] at hs
  have hreg : regionOfPath (mkSpec n) [] = some R := by simp [regionOfPath, hR']
  rw [hreg] at hs
  exact halfClaim_of_rootOK (covered_wf h) hR' (hs R (by simp))

end Autocorr.Cert
