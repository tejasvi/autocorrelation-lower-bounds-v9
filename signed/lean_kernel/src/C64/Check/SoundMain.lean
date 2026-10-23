import C64.Check.SoundH
import C64.Reduction

/-!
# Soundness of the checker, part 9: the global conditions, the cover of `[0, 1]`, and the main theorem

`main_of_checks`: if `checkGlob g`, `coverOK` of the arc list and `checkArc g a` for every arc hold, then
`ess sup (f ⋆ f) > (∫ f)² / (1 - τ)` for every admissible `f` with `∫ f ≠ 0`.  The consequences for the statements
of `C64.Defs` (with `τ = 7/30`) are `mainStatement_of`, `mainStatementEss_of`, `constStatement_of`.
-/

namespace C64Chk

open MeasureTheory Ival Ival.Ball C64Num Real

/-! ### The cover of `[0, 1]` -/

/-- An arc `[s₀, s₁]` of the grid `2^{-ES}` as reals. -/
noncomputable def toR (ES : ℕ) (p : ℕ × ℕ) : ℝ × ℝ := ((p.1 : ℝ) / 2 ^ ES, (p.2 : ℝ) / 2 ^ ES)

theorem coverOK_ok (g : Glob) : ∀ (x : ℕ) (L : List (ℕ × ℕ)), coverOK g x L = true →
    (∀ p ∈ (L.map (toR g.ES)).head?, p.1 = (x : ℝ) / 2 ^ g.ES) ∧ C64.CoversUnit (L.map (toR g.ES))
  | _, [], h => by simp [coverOK] at h
  | x, [(a, b)], h => by
    simp only [coverOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [toR], ?_⟩
    simp only [List.map_cons, List.map_nil, C64.CoversUnit, toR]
    push_cast; exact div_self (by positivity)
  | x, (a, b) :: q :: rest, h => by
    simp only [coverOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h'⟩ := h
    obtain ⟨hhead, hcov⟩ := coverOK_ok g b (q :: rest) h'
    refine ⟨by simp [toR], ?_⟩
    simp only [List.map_cons] at hcov hhead ⊢
    refine ⟨?_, hcov⟩
    have := hhead (toR g.ES q) (by simp)
    simp only [toR] at this ⊢
    rw [this]

/-! ### The winding number of `S` along `T₁` -/

theorem glob_winding {g : Glob} (hg : GlobOK g) (h : windOdd g (T1B g) [] 0 = true) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1, C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) ≠ 0) ∧
    ∃ n : ℤ, Odd n ∧ C64.HasWinding (fun s => C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s)) n := by
  have hA : AtomsOK [] := fun a ha => by simp at ha
  obtain ⟨h1, n, hn, hw⟩ := windOdd_ok hg (T1_ok hg) hA (by simp [msum]) h
  have e : ∀ z, C64.S z - wsum [] z = C64.S z := fun z => by simp [wsum]
  simp only [e] at h1 hw
  exact ⟨h1, n, hn, hw⟩

/-! ### The main theorem -/

theorem main_of_checks {g : Glob} {arcs : List Arc} (hG : checkGlob g = true)
    (hcov : coverOK g 0 (arcs.map fun a => (a.s0, a.s1)) = true) (hall : ∀ a ∈ arcs, checkArc g a = true) :
    ∀ f : ℝ → ℝ, C64.Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
      (∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ M) → (∫ x, f x) ^ 2 / (1 - g.tau.val) < M := by
  obtain ⟨hg, hw⟩ := checkGlob_ok hG
  obtain ⟨hS0, hSwind⟩ := glob_winding hg hw
  have ha : 0 < g.a.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.an) (by exact_mod_cast hg.ad)
  have hb : 0 < g.b.val := by unfold Q.val; exact div_pos (by exact_mod_cast hg.bn) (by exact_mod_cast hg.bd)
  obtain ⟨hhead, hcovR⟩ := coverOK_ok g 0 _ hcov
  have hmap : (arcs.map fun a => (a.s0, a.s1)).map (toR g.ES) =
      arcs.map fun a => ((a.s0 : ℝ) / 2 ^ g.ES, (a.s1 : ℝ) / 2 ^ g.ES) := by
    simp [List.map_map, toR, Function.comp_def]
  rw [hmap] at hhead hcovR
  refine C64.arcReduction g.tau.val g.c.val g.a.val g.b.val (tau_pos hg) (tau_lt_one hg) ha hb hS0 hSwind _
    (fun p hp => by simpa using hhead p hp) hcovR (fun p hp => ?_)
  obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hp
  exact checkArc_ok hg a (hall a ha')

/-! ### The statements of `C64.Defs` -/

theorem mainStatement_of {g : Glob} (hτ : g.tau.val = 7 / 30)
    (h : ∀ f : ℝ → ℝ, C64.Admissible f → ∫ x, f x ≠ 0 → ∀ M : ℝ,
      (∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ M) → (∫ x, f x) ^ 2 / (1 - g.tau.val) < M) :
    C64.MainStatement := by
  intro f hf hint M hM
  have := h f hf hint M hM
  rw [hτ] at this
  calc (30 / 23 : ℝ) * (∫ x, f x) ^ 2 = (∫ x, f x) ^ 2 / (1 - 7 / 30) := by ring
    _ < M := this

theorem mainStatementEss_of (h : C64.MainStatement) : C64.MainStatementEss := by
  intro f hf hint
  refine ⟨?_, ?_⟩
  · by_contra hc
    push Not at hc
    set x : ℝ := (30 / 23 : ℝ) * (∫ x, f x) ^ 2
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ x := by
      filter_upwards [ae_le_essSup (f := fun t => ((C64.autoconv f t : ℝ) : EReal))] with t ht
      exact EReal.coe_le_coe_iff.1 (ht.trans hc)
    exact lt_irrefl _ (h f hf hint x hae)
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun t =>
      EReal.coe_le_coe_iff.2 (le_abs_self _))

/-- An a.e. upper bound of `f ⋆ f` is nonnegative (`f ⋆ f` vanishes outside `[-1/2, 1/2]`). -/
theorem bound_nonneg {f : ℝ → ℝ} (hf : C64.Admissible f) {M : ℝ}
    (hM : ∀ᵐ t ∂(volume : Measure ℝ), C64.autoconv f t ≤ M) : 0 ≤ M := by
  by_contra hneg
  push Not at hneg
  have hzero : ∀ t ∈ Set.Ioi (1 : ℝ), C64.autoconv f t = 0 := by
    intro t ht
    exact C64.autoconv_eq_zero hf (fun h' => by have := h'.2; simp at ht; linarith)
  have hpos : (0 : ENNReal) < volume (Set.Ioi (1 : ℝ)) := by simp
  have : ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))), False := by
    filter_upwards [ae_restrict_of_ae hM, ae_restrict_mem measurableSet_Ioi] with t ht ht'
    rw [hzero t ht'] at ht; linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at this
  exact absurd this hpos.ne'

theorem constStatement_of (h : C64.MainStatement) : C64.ConstStatement := by
  have hvalid : C64.ValidC3' (30 / 23) := by
    intro f hf M hM
    by_cases hint : ∫ x, f x = 0
    · rw [hint]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact bound_nonneg hf hM
    · exact (h f hf hint M hM).le
  have hsub : ∀ C : ℝ, C64.ValidC3' C → C64.ValidC3 C := by
    intro C hC f hf M hM
    exact hC f hf M (hM.mono fun t ht => (le_abs_self _).trans ht)
  refine ⟨le_sSup ⟨_, hvalid, rfl⟩, sSup_le_sSup ?_⟩
  rintro _ ⟨C, hC, rfl⟩
  exact ⟨C, hsub C hC, rfl⟩

end C64Chk
