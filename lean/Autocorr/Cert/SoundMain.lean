import Autocorr.Cert.SoundRows
import Autocorr.Defs

/-!
# Soundness, part 3: weak duality, the stack machine, and `HalfClaim`

* `dualBound_le`: the NS bound computed by the checker is at most the value of the objective at any
  admissible point of the box (the true point with any `t ∈ [0,3]` dominating all windows).
* `run_sound`: if the stack machine turns the stack `stkIn` into `stkOut`, then every box of
  `stkIn` is covered (every admissible point in it has a window with `q_W ≥ lam`) provided every box
  of `stkOut` is.
* `halfClaim_of_rootOK`: covering the root box is `HalfClaim n lam`.
-/

open scoped BigOperators

namespace Autocorr.Cert

variable {sp : Spec}

/-! ## Weak duality -/

/-- `Σ_{k < NC} r_k x_k`. -/
noncomputable def dot (sp : Spec) (r : Array ℚ) (x : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range sp.NC, ((r.getD k 0 : ℚ) : ℝ) * x k

lemma dot_modify (r : Array ℚ) (hr : r.size = sp.NC) {k : ℕ} (hk : k < sp.NC) (v : ℚ)
    (x : ℕ → ℝ) : dot sp (r.modify k (· + v)) x = dot sp r x + (v : ℝ) * x k := by
  unfold dot
  have : ∀ j ∈ Finset.range sp.NC, (((r.modify k (· + v)).getD j 0 : ℚ) : ℝ) * x j =
      ((r.getD j 0 : ℚ) : ℝ) * x j + (if k = j then (v : ℝ) * x j else 0) := by
    intro j _
    rw [getD_modify r k j _ 0 (by rw [hr]; exact hk)]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [Finset.mem_range.mpr hk]

lemma scatter_spec (c : ℚ) (x : ℕ → ℝ) :
    ∀ (ent : List (ℕ × ℚ)) (r : Array ℚ), r.size = sp.NC → (∀ e ∈ ent, e.1 < sp.NC) →
      (scatter r c ent).size = sp.NC ∧
      dot sp (scatter r c ent) x = dot sp r x + (c : ℝ) * rowVal ent x := by
  intro ent
  induction ent with
  | nil => intro r hr _; simp [scatter, hr]
  | cons e rest ih =>
    intro r hr hent
    obtain ⟨k, a⟩ := e
    have hk : k < sp.NC := hent (k, a) (List.mem_cons_self ..)
    have hr' : (r.modify k (· + c * a)).size = sp.NC := by rw [Array.size_modify, hr]
    obtain ⟨h1, h2⟩ := ih _ hr' (fun e he => hent e (List.mem_cons_of_mem _ he))
    refine ⟨h1, ?_⟩
    simp only [scatter]
    rw [h2, dot_modify r hr hk, rowVal_cons]
    push_cast; ring

lemma entOK_spec {ent : List (ℕ × ℚ)} (h : entOK sp ent = true) : ∀ e ∈ ent, e.1 < sp.NC := by
  intro e he
  have := List.all_eq_true.mp h e he
  simpa using this

section Duality

variable {p : ℕ → ℝ} {t : ℝ} {bx : Box}

/-- Invariant of the dual fold: `acc + Σ r_k x_k` never increases. -/
lemma foldl_dualStep_spec (hrow : ∀ key, keyOK sp key = true →
      RowValid (rowOf sp bx key) (rowVal (rowOf sp bx key).ent (xval sp p t))) (V : ℝ) :
    ∀ (ys : List (RowKey × ℚ)) (st : ℚ × Array ℚ), st.2.size = sp.NC →
      ((st.1 : ℝ) + dot sp st.2 (xval sp p t) ≤ V) →
      (ys.foldl (dualStep sp bx) st).2.size = sp.NC ∧
      (((ys.foldl (dualStep sp bx) st).1 : ℚ) : ℝ) +
        dot sp (ys.foldl (dualStep sp bx) st).2 (xval sp p t) ≤ V := by
  intro ys
  induction ys with
  | nil => intro st h1 h2; exact ⟨h1, h2⟩
  | cons ky rest ih =>
    intro st hsz hinv
    rw [List.foldl_cons]
    apply ih
    · -- size
      unfold dualStep
      split_ifs with hok h0 h0'
      · rw [Bool.and_eq_true] at hok
        cases hlo : (rowOf sp bx ky.1).lo with
        | none => exact hsz
        | some l => exact (scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)).1
      · rw [Bool.and_eq_true] at hok
        cases hup : (rowOf sp bx ky.1).up with
        | none => exact hsz
        | some u => exact (scatter_spec (sp := sp) (-ky.2) (xval sp p t) _ _ hsz (entOK_spec hok.2)).1
      · exact hsz
      · exact hsz
    · -- value
      unfold dualStep
      split_ifs with hok h0 h0'
      · rw [Bool.and_eq_true] at hok
        have hv := (hrow ky.1 hok.1).1
        cases hlo : (rowOf sp bx ky.1).lo with
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
        cases hup : (rowOf sp bx ky.1).up with
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

lemma foldl_add_eq (g : ℕ → ℚ) (l : List ℕ) (a : ℚ) :
    l.foldl (fun acc k => acc + g k) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

lemma list_sum_range (g : ℕ → ℚ) (m : ℕ) : ((List.range m).map g).sum = ∑ k ∈ Finset.range m, g k := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma colPart_le (hp : Adm sp p) (hbx : InBox sp p bx) (ht0 : 0 ≤ t) (ht3 : t ≤ 3) (r : Array ℚ) :
    ((colPart sp bx r : ℚ) : ℝ) ≤ dot sp r (xval sp p t) := by
  unfold colPart dot
  rw [foldl_add_eq, zero_add, list_sum_range]
  push_cast
  refine Finset.sum_le_sum (fun k _ => ?_)
  obtain ⟨hlb, hub⟩ := col_bounds hp hbx ht0 ht3 k
  rcases le_total 0 ((r.getD k 0 : ℚ) : ℝ) with hr | hr
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlb hr)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hub hr)

lemma dot_r0 (obj : Bool) (x : ℕ → ℝ) :
    dot sp (if obj then (Array.replicate sp.NC (0 : ℚ)).setIfInBounds sp.oT 1
      else Array.replicate sp.NC (0 : ℚ)) x = if obj then x sp.oT else 0 := by
  unfold dot
  have hT : sp.oT < sp.NC := by rw [NC_eq]; omega
  cases obj
  · simp only [Bool.false_eq_true, if_false]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    rw [Finset.mem_range] at hk
    simp [hk]
  · simp only [if_true]
    have : ∀ k ∈ Finset.range sp.NC,
        ((((Array.replicate sp.NC (0 : ℚ)).setIfInBounds sp.oT 1).getD k 0 : ℚ) : ℝ) * x k =
        if sp.oT = k then x k else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [getD_setIfInBounds, Array.size_replicate, Array.getD_eq_getD_getElem?,
        Array.getElem?_replicate]
      by_cases h : sp.oT = k
      · simp [h, hk]
      · simp [h, hk]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [Finset.mem_range.mpr hT]

/-- Weak duality: the checker's bound is at most the objective at the true point. -/
theorem dualBound_le (hw : sp.wf = true) (hp : Adm sp p) (hbx : InBox sp p bx)
    (ht0 : 0 ≤ t) (ht3 : t ≤ 3)
    (hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t)
    (obj : Bool) (ys : List (RowKey × ℚ)) :
    ((dualBound sp bx obj ys : ℚ) : ℝ) ≤ if obj then t else 0 := by
  have hrow := fun key hk => row_valid (t := t) hw hp hbx hwin key hk
  unfold dualBound
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
  obtain ⟨h1, h2⟩ := foldl_dualStep_spec hrow _ ys (0, r0) hsz hV
  have h3 := colPart_le hp hbx ht0 ht3 (ys.foldl (dualStep sp bx) (0, r0)).2
  push_cast
  linarith

end Duality

/-! ## Covering boxes -/

/-- Some window certifies `lam` at `p`. -/
def Good (sp : Spec) (lam : ℝ) (p : ℕ → ℝ) : Prop :=
  ∃ c1 c2, c1 ≤ c2 ∧ c2 + 2 ≤ 2 * sp.n ∧ lam * ((c2 : ℝ) - c1 + 2) ≤ 2 * sp.n * wsum sp p c1 c2

/-- Every admissible point of the box is good. -/
def BoxOK (sp : Spec) (lam : ℝ) (bx : Box) : Prop :=
  ∀ p, Adm sp p → InBox sp p bx → Good sp lam p

def StackOK (sp : Spec) (lam : ℝ) (stk : List Box) : Prop := ∀ bx ∈ stk, BoxOK sp lam bx

lemma wsum_nonneg {p : ℕ → ℝ} (hp : Adm sp p) (c1 c2 : ℕ) : 0 ≤ wsum sp p c1 c2 := by
  unfold wsum
  exact (sum_mul_sum_le_one hp _).1

/-- If the bound with the objective `t` is at least `lam`, the box is covered. -/
theorem leaf_sound (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) {bx : Box}
    {ys : List (RowKey × ℚ)} (hlb : lam ≤ dualBound sp bx true ys) : BoxOK sp lam bx := by
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
  have hb := dualBound_le hw hp hbx ht0 ht3 hwin true ys
  simp only [if_true] at hb
  have : ((lam : ℚ) : ℝ) ≤ ((dualBound sp bx true ys : ℚ) : ℝ) := by exact_mod_cast hlb
  linarith

/-- A positive Farkas bound (zero objective) excludes every point with `F(p) < lam ≤ 3`. -/
theorem farkas_sound (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) {bx : Box}
    {ys : List (RowKey × ℚ)} (hlb : 0 < dualBound sp bx false ys) : BoxOK sp lam bx := by
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
  have hb := dualBound_le hw hp hbx ht0 ht3 hwin false ys
  simp only [Bool.false_eq_true, if_false] at hb
  have : (0 : ℝ) < ((dualBound sp bx false ys : ℚ) : ℝ) := by exact_mod_cast hlb
  linarith

/-- Every admissible point of a box lies in one of the two children of a split. -/
theorem child_cover (hw : sp.wf = true) {p : ℕ → ℝ} (hp : Adm sp p) {bx : Box}
    (hbx : InBox sp p bx) (b : ℕ) (s : ℚ) :
    (∃ c, child sp bx b s false = some c ∧ InBox sp p c) ∨
    (∃ c, child sp bx b s true = some c ∧ InBox sp p c) := by
  by_cases hs : mass sp p b ≤ (s : ℝ)
  · left
    unfold child
    simp only [Bool.false_eq_true, if_false]
    exact propagate_sound hw hp _ _ hbx.1 (up_set hbx.2 (fun _ => hs))
  · right
    unfold child
    simp only [if_true]
    exact propagate_sound hw hp _ _ (low_set hbx.1 (fun _ => (lt_of_not_ge hs).le)) hbx.2

/-- The stack machine is sound. -/
theorem run_sound (hw : sp.wf = true) {lam : ℚ} (hlam : lam ≤ 3) :
    ∀ (recs : List Rec) (stk stk' : List Box), run sp lam recs stk = some stk' →
      StackOK sp lam stk' → StackOK sp lam stk := by
  intro recs
  induction recs with
  | nil =>
    intro stk stk' h hok
    simp only [run, Option.some.injEq] at h
    rw [h]; exact hok
  | cons r rs ih =>
    intro stk stk' h hok
    cases stk with
    | nil => simp [run] at h
    | cons bx stk =>
      cases r with
      | split b s =>
        simp only [run] at h
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · intro p hp hpb
          rcases child_cover hw hp hpb b s with ⟨c, hc, hpc⟩ | ⟨c, hc, hpc⟩
          · exact hall c (by simp [hc]) p hp hpc
          · exact hall c (by simp [hc]) p hp hpc
        · exact hall bx' (by simp [hin])
      | leaf ys =>
        simp only [run] at h
        split_ifs at h with hlb
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · exact leaf_sound hw hlam hlb
        · exact hall bx' hin
      | farkas ys =>
        simp only [run] at h
        split_ifs at h with hlb
        have hall := ih _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · exact farkas_sound hw hlam hlb
        · exact hall bx' hin
      | deleg =>
        simp only [run] at h
        cases hr : run sp lam rs stk with
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

theorem checkSeg_sound {lam : ℚ} {stkIn : List Box} {recs : List Rec} {stkOut : List Box}
    (h : checkSeg sp lam stkIn recs stkOut = true) :
    StackOK sp lam stkOut → StackOK sp lam stkIn := by
  simp only [checkSeg, Bool.and_eq_true, decide_eq_true_eq] at h
  exact run_sound h.1.1 h.1.2 recs stkIn stkOut h.2

/-! ## The root box and `HalfClaim` -/

theorem rootBox_sound (hw : sp.wf = true) {R : Box} (hR : rootBox sp = some R) {p : ℕ → ℝ}
    (hp : Adm sp p) : InBox sp p R := by
  have hL : LowOK sp p (Array.replicate sp.nB (0 : ℚ)) := by
    intro b hb
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    simp [hb, mass_nonneg hp b]
  have hU : UpOK sp p (Array.replicate sp.nB (1 : ℚ)) := by
    intro b hb
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    simp [hb, mass_le_one hp b]
  obtain ⟨bx, hbx, hin⟩ := propagate_sound hw hp _ _ hL hU
  unfold rootBox at hR
  rw [hbx, Option.some.injEq] at hR
  rw [← hR]; exact hin

/-- Covering the root box is the half-space claim. -/
theorem halfClaim_of_rootOK (hw : sp.wf = true) {R : Box} (hR : rootBox sp = some R) {lam : ℝ}
    (hok : BoxOK sp lam R) : Autocorr.HalfClaim sp.n lam := by
  intro q hq hsum hhalf
  set p : ℕ → ℝ := fun i => if h : i < sp.n then q ⟨i, h⟩ else 0 with hpdef
  have hpq : ∀ i : Fin sp.n, p i = q i := fun i => by simp [hpdef, i.isLt]
  have hsumR : ∀ f : ℕ → ℝ, ∑ i : Fin sp.n, f i = ∑ i ∈ Finset.range sp.n, f i :=
    fun f => Fin.sum_univ_eq_sum_range f sp.n
  have hp : Adm sp p := by
    refine ⟨fun i => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [hpdef]; split_ifs
      · exact hq _
      · exact le_refl 0
    · simp only [hpdef]; rw [dif_neg (by omega)]
    · rw [← hsumR p, ← hsum]
      exact Finset.sum_congr rfl (fun i _ => hpq i)
    · rw [← hsumR (fun i => (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * p i)]
      calc ∑ i : Fin sp.n, (2 * ((i : ℕ) : ℝ) - ((sp.n : ℝ) - 1)) * p i
          = ∑ i : Fin sp.n, (2 * ((i : ℕ) : ℝ) - ((sp.n : ℝ) - 1)) * q i :=
            Finset.sum_congr rfl (fun i _ => by rw [hpq i])
        _ ≤ 0 := hhalf
  obtain ⟨c1, c2, h12, h2, hineq⟩ := hok p hp (rootBox_sound hw hR hp)
  refine ⟨c1, c2, h12, h2, ?_⟩
  have hws : wsum sp p c1 c2 = Autocorr.winSum q c1 c2 := by
    unfold wsum Autocorr.winSum
    rw [← hsumR]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hsumR (fun j => if c1 ≤ (i : ℕ) + j ∧ (i : ℕ) + j ≤ c2 then p i * p j else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hpq i, hpq j]
  rw [← hws]
  exact hineq

end Autocorr.Cert
