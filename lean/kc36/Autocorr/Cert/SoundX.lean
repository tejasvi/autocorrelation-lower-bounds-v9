import AutocorrCert.DecodeX
import Autocorr.Cert.CoveredSound

/-!
# Soundness of the extended checker (square-cut rows; `AutocorrCert/CheckerX.lean`)

`valid_sq`: a square-cut row holds at the true point, since its left side plus `v0²` is
`(v0 + Σ_a v_a m_{B_a})²` when every product column equals the product of the block masses (`xval_canon`).
The rest repeats `SoundMain.lean` / `CoveredSound.lean` with `XKey`, `dualStepX`, `runX`, `CoveredX`.
-/

open scoped BigOperators

namespace Autocorr.Cert

variable {sp : Spec}

/-- `Σ_a v_a m_{B_a}`. -/
noncomputable def sqS (sp : Spec) (p : ℕ → ℝ) (terms : List (ℕ × ℤ)) : ℝ :=
  (terms.map (fun t => (t.2 : ℝ) * mass sp p t.1)).sum

lemma rowVal_map' (l : List (ℕ × ℤ)) (f : ℕ × ℤ → ℕ × ℚ) (x : ℕ → ℝ) :
    rowVal (l.map f) x = (l.map (fun e => (((f e).2 : ℚ) : ℝ) * x (f e).1)).sum := by
  simp [rowVal, List.map_map, Function.comp_def]

lemma rowVal_sqEnt (hw : sp.wf = true) {p : ℕ → ℝ} {t : ℝ} (v0 : ℤ) :
    ∀ (terms : List (ℕ × ℤ)), (∀ e ∈ terms, e.1 < sp.nB) →
      rowVal (sqEnt sp v0 terms) (xval sp p t) = sqS sp p terms ^ 2 + 2 * v0 * sqS sp p terms := by
  intro terms
  induction terms with
  | nil => intro _; simp [sqEnt, sqS]
  | cons e rest ih =>
    intro hb
    obtain ⟨b, v⟩ := e
    have hb0 : b < sp.nB := hb (b, v) (List.mem_cons_self ..)
    have hrest : ∀ e ∈ rest, e.1 < sp.nB := fun e he => hb e (List.mem_cons_of_mem _ he)
    have hmap : rowVal (rest.map (fun t => (sp.canon b t.1, 2 * (v : ℚ) * t.2))) (xval sp p t) =
        2 * (v : ℝ) * mass sp p b * sqS sp p rest := by
      rw [rowVal_map', sqS, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left (fun e he => ?_)
      rw [xval_canon hw hb0 (hrest e he)]
      push_cast; ring
    simp only [sqEnt]
    rw [rowVal_cons, rowVal_cons, rowVal_append, hmap, ih hrest, xval_canon hw hb0 hb0, xval_m hb0]
    simp only [sqS, List.map_cons, List.sum_cons]
    push_cast
    ring

lemma valid_sq (hw : sp.wf = true) {p : ℕ → ℝ} {t : ℝ} {bx : Box} {v0 : ℤ} {terms : List (ℕ × ℤ)}
    (hk : keyOKX sp (.sq v0 terms) = true) :
    RowValid (rowOfX sp bx (.sq v0 terms)) (rowVal (rowOfX sp bx (.sq v0 terms)).ent (xval sp p t)) := by
  simp only [keyOKX, List.all_eq_true, decide_eq_true_eq] at hk
  simp only [rowOfX]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · simp only [Option.some.injEq] at hl
    subst hl
    rw [rowVal_sqEnt hw v0 terms hk]
    push_cast
    nlinarith [sq_nonneg (sqS sp p terms + v0)]
  · simp at hu

theorem row_validX (hw : sp.wf = true) {p : ℕ → ℝ} (hp : Adm sp p) {t : ℝ} {bx : Box} (hbx : InBox sp p bx)
    (hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t)
    (key : XKey) (hk : keyOKX sp key = true) :
    RowValid (rowOfX sp bx key) (rowVal (rowOfX sp bx key).ent (xval sp p t)) := by
  cases key with
  | base k => exact row_valid hw hp hbx hwin k hk
  | sq v0 terms => exact valid_sq hw hk

section Duality

variable {p : ℕ → ℝ} {t : ℝ} {bx : Box}

/-- Invariant of the dual fold: `acc + Σ r_k x_k` never increases. -/
lemma foldl_dualStepX_spec (hrow : ∀ key, keyOKX sp key = true →
      RowValid (rowOfX sp bx key) (rowVal (rowOfX sp bx key).ent (xval sp p t))) (V : ℝ) :
    ∀ (ys : List (XKey × ℚ)) (st : ℚ × Array ℚ), st.2.size = sp.NC →
      ((st.1 : ℝ) + dot sp st.2 (xval sp p t) ≤ V) →
      (ys.foldl (dualStepX sp bx) st).2.size = sp.NC ∧
      (((ys.foldl (dualStepX sp bx) st).1 : ℚ) : ℝ) +
        dot sp (ys.foldl (dualStepX sp bx) st).2 (xval sp p t) ≤ V := by
  intro ys
  induction ys with
  | nil => intro st h1 h2; exact ⟨h1, h2⟩
  | cons ky rest ih =>
    intro st hsz hinv
    rw [List.foldl_cons]
    apply ih
    · -- size
      unfold dualStepX
      split_ifs with hok h0 h0'
      · rw [Bool.and_eq_true] at hok
        cases hlo : (rowOfX sp bx ky.1).lo with
        | none => exact hsz
        | some l => exact (scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)).1
      · rw [Bool.and_eq_true] at hok
        cases hup : (rowOfX sp bx ky.1).up with
        | none => exact hsz
        | some u => exact (scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)).1
      · exact hsz
      · exact hsz
    · -- value
      unfold dualStepX
      split_ifs with hok h0 h0'
      · rw [Bool.and_eq_true] at hok
        have hv := (hrow ky.1 hok.1).1
        cases hlo : (rowOfX sp bx ky.1).lo with
        | none => exact hinv
        | some l =>
          obtain ⟨-, hd⟩ := scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)
          simp only
          rw [hd]
          have hl := hv l hlo
          have hy : (0 : ℝ) < ky.2 := by exact_mod_cast h0
          push_cast
          nlinarith
      · rw [Bool.and_eq_true] at hok
        have hv := (hrow ky.1 hok.1).2
        cases hup : (rowOfX sp bx ky.1).up with
        | none => exact hinv
        | some u =>
          obtain ⟨-, hd⟩ := scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)
          simp only
          rw [hd]
          have hu := hv u hup
          have hy : (ky.2 : ℝ) < 0 := by exact_mod_cast h0'
          push_cast
          nlinarith
      · exact hinv
      · exact hinv

/-- Weak duality: the checker's bound is at most the objective at the true point. -/
theorem dualBoundX_le (hw : sp.wf = true) (hp : Adm sp p) (hbx : InBox sp p bx)
    (ht0 : 0 ≤ t) (ht3 : t ≤ 3)
    (hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t)
    (obj : Bool) (ys : List (XKey × ℚ)) :
    ((dualBoundX sp bx obj ys : ℚ) : ℝ) ≤ if obj then t else 0 := by
  have hrow := fun key hk => row_validX (t := t) hw hp hbx hwin key hk
  unfold dualBoundX
  simp only
  set r0 := if obj then (Array.replicate sp.NC (0 : ℚ)).setIfInBounds sp.oT 1
    else Array.replicate sp.NC (0 : ℚ) with hr0
  have hsz : r0.size = sp.NC := by
    rw [hr0]; split_ifs <;> simp [Array.size_setIfInBounds]
  have hV : ((0 : ℚ) : ℝ) + dot sp r0 (xval sp p t) ≤ if obj then t else 0 := by
    rw [hr0, dot_r0, Rat.cast_zero, zero_add]
    split_ifs
    · rw [xval_T]
    · exact le_refl _
  obtain ⟨h1, h2⟩ := foldl_dualStepX_spec hrow _ ys (0, r0) hsz hV
  have h3 := colPart_le hp hbx ht0 ht3 (ys.foldl (dualStepX sp bx) (0, r0)).2
  push_cast
  linarith

end Duality

/-- If the bound with the objective `t` is at least `lam`, the box is covered. -/
theorem leaf_soundX (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) {bx : Box}
    {ys : List (XKey × ℚ)} (hlb : lam ≤ dualBoundX sp bx true ys) : BoxOK sp lam bx := by
  intro p hp hbx
  by_contra hng
  have hn := sp.wf_n_pos hw
  -- the windows
  set W := (Finset.range (2 * sp.n - 1) ×ˢ Finset.range (2 * sp.n - 1)).filter
    (fun c : ℕ × ℕ => c.1 ≤ c.2) with hW
  have hWne : W.Nonempty := ⟨(0, 0), by simp [hW]; omega⟩
  set val : ℕ × ℕ → ℝ := fun c => 2 * (sp.n : ℝ) / ((c.2 : ℝ) - c.1 + 2) * wsum sp p c.1 c.2
    with hval
  obtain ⟨cm, hcm, hmax⟩ := Finset.exists_max_image W val hWne
  have hmem : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n → (c1, c2) ∈ W := by
    intro c1 c2 h12 h2
    simp [hW]; omega
  have hcm' : cm.1 ≤ cm.2 ∧ cm.2 + 2 ≤ 2 * sp.n := by
    simp [hW] at hcm; omega
  have hpos : ∀ c : ℕ × ℕ, c.1 ≤ c.2 → (0 : ℝ) < (c.2 : ℝ) - c.1 + 2 := by
    intro c hc
    have : (c.1 : ℝ) ≤ c.2 := by exact_mod_cast hc
    linarith
  set t := val cm with ht
  have ht0 : 0 ≤ t := by
    rw [ht, hval]
    exact mul_nonneg (div_nonneg (by positivity) (hpos cm hcm'.1).le) (wsum_nonneg hp _ _)
  have htlam : t < lam := by
    by_contra hge
    push Not at hge
    apply hng
    refine ⟨cm.1, cm.2, hcm'.1, hcm'.2, ?_⟩
    have hk := hpos cm hcm'.1
    rw [ht, hval] at hge
    simp only at hge
    rw [div_mul_eq_mul_div, le_div_iff₀ hk] at hge
    linarith
  have ht3 : t ≤ 3 := by
    have : ((lam : ℚ) : ℝ) ≤ 3 := by exact_mod_cast hlam
    linarith
  have hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t :=
    fun c1 c2 h12 h2 => hmax (c1, c2) (hmem c1 c2 h12 h2)
  have hb := dualBoundX_le hw hp hbx ht0 ht3 hwin true ys
  simp only [if_true] at hb
  have : ((lam : ℚ) : ℝ) ≤ ((dualBoundX sp bx true ys : ℚ) : ℝ) := by exact_mod_cast hlb
  linarith

/-- A positive Farkas bound (zero objective) excludes every point with `F(p) < lam ≤ 3`. -/
theorem farkas_soundX (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) {bx : Box}
    {ys : List (XKey × ℚ)} (hlb : 0 < dualBoundX sp bx false ys) : BoxOK sp lam bx := by
  intro p hp hbx
  by_contra hng
  have hn := sp.wf_n_pos hw
  set W := (Finset.range (2 * sp.n - 1) ×ˢ Finset.range (2 * sp.n - 1)).filter
    (fun c : ℕ × ℕ => c.1 ≤ c.2) with hW
  have hWne : W.Nonempty := ⟨(0, 0), by simp [hW]; omega⟩
  set val : ℕ × ℕ → ℝ := fun c => 2 * (sp.n : ℝ) / ((c.2 : ℝ) - c.1 + 2) * wsum sp p c.1 c.2
    with hval
  obtain ⟨cm, hcm, hmax⟩ := Finset.exists_max_image W val hWne
  have hmem : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n → (c1, c2) ∈ W := by
    intro c1 c2 h12 h2
    simp [hW]; omega
  have hcm' : cm.1 ≤ cm.2 ∧ cm.2 + 2 ≤ 2 * sp.n := by
    simp [hW] at hcm; omega
  have hpos : ∀ c : ℕ × ℕ, c.1 ≤ c.2 → (0 : ℝ) < (c.2 : ℝ) - c.1 + 2 := by
    intro c hc
    have : (c.1 : ℝ) ≤ c.2 := by exact_mod_cast hc
    linarith
  set t := val cm with ht
  have ht0 : 0 ≤ t := by
    rw [ht, hval]
    exact mul_nonneg (div_nonneg (by positivity) (hpos cm hcm'.1).le) (wsum_nonneg hp _ _)
  have htlam : t < lam := by
    by_contra hge
    push Not at hge
    apply hng
    refine ⟨cm.1, cm.2, hcm'.1, hcm'.2, ?_⟩
    have hk := hpos cm hcm'.1
    rw [ht, hval] at hge
    simp only at hge
    rw [div_mul_eq_mul_div, le_div_iff₀ hk] at hge
    linarith
  have ht3 : t ≤ 3 := by
    have : ((lam : ℚ) : ℝ) ≤ 3 := by exact_mod_cast hlam
    linarith
  have hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t :=
    fun c1 c2 h12 h2 => hmax (c1, c2) (hmem c1 c2 h12 h2)
  have hb := dualBoundX_le hw hp hbx ht0 ht3 hwin false ys
  simp only [Bool.false_eq_true, if_false] at hb
  have : (0 : ℝ) < ((dualBoundX sp bx false ys : ℚ) : ℝ) := by exact_mod_cast hlb
  linarith

/-- The stack machine is sound. -/
theorem runX_sound (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) (zo : List RowKey) :
    ∀ (recs : List RecX) (stk stk' : List Box), runX sp lam zo recs stk = some stk' →
      StackOK sp lam stk' → StackOK sp lam stk := by
  intro recs
  induction recs with
  | nil =>
    intro stk stk' h hok
    simp only [runX, Option.some.injEq] at h
    rw [h]; exact hok
  | cons r rs ih =>
    intro stk stk' h hok
    cases stk with
    | nil => simp [runX] at h
    | cons bx stk =>
      cases r with
      | split b s =>
        simp only [runX] at h
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · intro p hp hpb
          rcases child_cover hw hp hpb b s with ⟨c, hc, hpc⟩ | ⟨c, hc, hpc⟩
          · exact hall c (by simp [hc]) p hp hpc
          · exact hall c (by simp [hc]) p hp hpc
        · exact hall bx' (by simp [hin])
      | leaf ys =>
        simp only [runX] at h
        split_ifs at h with hlb
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · exact leaf_soundX hw hlam hlb
        · exact hall bx' hin
      | farkas ys =>
        simp only [runX] at h
        split_ifs at h with hlb
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · exact farkas_soundX hw hlam hlb
        · exact hall bx' hin
      | deleg =>
        simp only [runX] at h
        cases hr : runX sp lam zo rs stk with
        | none => rw [hr] at h; simp at h
        | some out =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hall := ih _ _ hr (fun b hb => hok b (List.mem_cons_of_mem _ hb))
          intro bx' hbx'
          rcases List.mem_cons.mp hbx' with rfl | hin
          · exact hok bx' (List.mem_cons_self ..)
          · exact hall bx' hin
      | leafc ys =>
        simp only [runX] at h
        split_ifs at h with hlb
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · exact leaf_soundX hw hlam hlb
        · exact hall bx' hin

theorem coveredX_sound {n : ℕ} {lam : ℚ} {zo s : String} (h : CoveredX n lam zo s) :
    ∀ bx ∈ (regionOfPath (mkSpec n) (Dec.decodePath s)).toList, BoxOK (mkSpec n) lam bx := by
  induction h with
  | mk root children recs hchk hc ih =>
    unfold checkJobStrX checkJobX at hchk
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
    exact runX_sound hwf hlam _ (Dec.decodeRecsX recs) [bx] _ hrun hst bx (List.mem_singleton_self _)

theorem coveredX_wf {n : ℕ} {lam : ℚ} {zo s : String} (h : CoveredX n lam zo s) : (mkSpec n).wf = true := by
  cases h with
  | mk root children recs hchk hc =>
    unfold checkJobStrX checkJobX at hchk
    simp only [Bool.and_eq_true] at hchk
    exact hchk.1.1

/-- The root job covers the whole half-space. -/
theorem halfClaim_of_coveredX {n : ℕ} {lam : ℚ} {zo : String} (h : CoveredX n lam zo "")
    (hR : (rootBox (mkSpec n)).isSome = true) : HalfClaim n (lam : ℝ) := by
  obtain ⟨R, hR'⟩ := Option.isSome_iff_exists.mp hR
  have hs := coveredX_sound h
  have hpath : Dec.decodePath "" = [] := rfl
  rw [hpath] at hs
  have hreg : regionOfPath (mkSpec n) [] = some R := by simp [regionOfPath, hR']
  rw [hreg] at hs
  exact halfClaim_of_rootOK (coveredX_wf h) hR' (hs R (by simp))

end Autocorr.Cert
