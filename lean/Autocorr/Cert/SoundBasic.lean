import Mathlib
import AutocorrCert.Checker

/-!
# Soundness, part 1: semantics of regions and soundness of interval propagation

Points are `p : ℕ → ℝ` that vanish from `n` on (`Adm`: nonnegative, sum 1, half-space).
`mass sp p b = Σ_{lo_b ≤ i < hi_b} p_i`; a box contains `p` if `L_b ≤ mass b ≤ U_b` for all `b < nB`
(bounds read with `getD`, so the statement makes sense for arrays of any size).
-/

open scoped BigOperators

namespace Autocorr.Cert

/-! ## Array lemmas -/

lemma getD_setIfInBounds {α : Type*} (xs : Array α) (i j : ℕ) (a d : α) :
    (xs.setIfInBounds i a).getD j d = if i = j ∧ i < xs.size then a else xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < xs.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

lemma getD_modify {α : Type*} (xs : Array α) (i j : ℕ) (f : α → α) (d : α) (hi : i < xs.size) :
    (xs.modify i f).getD j d = if i = j then f (xs.getD j d) else xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = j
  · subst h1
    simp [Array.getElem?_eq_getElem hi]
  · simp [h1]

lemma size_setIfInBounds' {α : Type*} (xs : Array α) (i : ℕ) (a : α) :
    (xs.setIfInBounds i a).size = xs.size := Array.size_setIfInBounds

/-! ## Well-formedness facts -/

namespace Spec

variable (sp : Spec)

lemma wf_unfold (h : sp.wf = true) :
    0 < sp.n ∧ 0 < sp.nB ∧ (sp.blk 0).lo = 0 ∧ (sp.blk 0).hi = sp.n ∧
    (∀ b < sp.nB, (sp.blk b).lo < (sp.blk b).hi ∧ (sp.blk b).hi ≤ sp.n ∧
      ((sp.blk b).hi = (sp.blk b).lo + 1 ∨
        ((sp.blk b).c1 < sp.nB ∧ (sp.blk b).c2 < sp.nB ∧
          (sp.blk (sp.blk b).c1).lo = (sp.blk b).lo ∧
          (sp.blk (sp.blk b).c1).hi = (sp.blk (sp.blk b).c2).lo ∧
          (sp.blk (sp.blk b).c2).hi = (sp.blk b).hi))) ∧
    (∀ i < sp.n, sp.leaf i < sp.nB ∧ (sp.blk (sp.leaf i)).lo = i ∧
      (sp.blk (sp.leaf i)).hi = i + 1) := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hG⟩ := h
  refine ⟨hA, hB, hC, hD, fun b hb => ?_, fun i hi => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hE b hb
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h3 | ⟨⟨⟨⟨h4, h5⟩, h6⟩, h7⟩, h8⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h4, h5, h6, h7, h8⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hG i hi
    exact ⟨h1, h2, h3⟩

lemma wf_n_pos (h : sp.wf = true) : 0 < sp.n := (sp.wf_unfold h).1

lemma wf_nB_pos (h : sp.wf = true) : 0 < sp.nB := (sp.wf_unfold h).2.1

lemma wf_root (h : sp.wf = true) : (sp.blk 0).lo = 0 ∧ (sp.blk 0).hi = sp.n :=
  ⟨(sp.wf_unfold h).2.2.1, (sp.wf_unfold h).2.2.2.1⟩

lemma wf_blk (h : sp.wf = true) {b : ℕ} (hb : b < sp.nB) :
    (sp.blk b).lo < (sp.blk b).hi ∧ (sp.blk b).hi ≤ sp.n ∧
    ((sp.blk b).hi = (sp.blk b).lo + 1 ∨
      ((sp.blk b).c1 < sp.nB ∧ (sp.blk b).c2 < sp.nB ∧
        (sp.blk (sp.blk b).c1).lo = (sp.blk b).lo ∧
        (sp.blk (sp.blk b).c1).hi = (sp.blk (sp.blk b).c2).lo ∧
        (sp.blk (sp.blk b).c2).hi = (sp.blk b).hi)) :=
  (sp.wf_unfold h).2.2.2.2.1 b hb

lemma wf_leaf (h : sp.wf = true) {i : ℕ} (hi : i < sp.n) :
    sp.leaf i < sp.nB ∧ (sp.blk (sp.leaf i)).lo = i ∧ (sp.blk (sp.leaf i)).hi = i + 1 :=
  (sp.wf_unfold h).2.2.2.2.2 i hi

/-- Children of an internal block. -/
lemma wf_int (h : sp.wf = true) {b : ℕ} (hb : b < sp.nB) (hint : sp.isInt b = true) :
    (sp.blk b).c1 < sp.nB ∧ (sp.blk b).c2 < sp.nB ∧
        (sp.blk (sp.blk b).c1).lo = (sp.blk b).lo ∧
        (sp.blk (sp.blk b).c1).hi = (sp.blk (sp.blk b).c2).lo ∧
        (sp.blk (sp.blk b).c2).hi = (sp.blk b).hi := by
  rcases (sp.wf_blk h hb).2.2 with h1 | h1
  · simp only [isInt, decide_eq_true_eq] at hint; omega
  · exact h1

end Spec

/-! ## Points and boxes -/

variable (sp : Spec)

/-- Admissible points: the simplex intersected with the half-space, extended by zero. -/
structure Adm (p : ℕ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  zero : ∀ i, sp.n ≤ i → p i = 0
  sum1 : ∑ i ∈ Finset.range sp.n, p i = 1
  half : ∑ i ∈ Finset.range sp.n, (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * p i ≤ 0

/-- Mass of block `b`. -/
noncomputable def mass (p : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (sp.blk b).lo (sp.blk b).hi, p i

/-- Lower and upper bound invariants for arrays of bounds. -/
def LowOK (p : ℕ → ℝ) (L : Array ℚ) : Prop := ∀ b < sp.nB, ((L.getD b 0 : ℚ) : ℝ) ≤ mass sp p b
def UpOK (p : ℕ → ℝ) (U : Array ℚ) : Prop := ∀ b < sp.nB, mass sp p b ≤ ((U.getD b 0 : ℚ) : ℝ)

def InBox (p : ℕ → ℝ) (bx : Box) : Prop := LowOK sp p bx.L ∧ UpOK sp p bx.U

variable {sp}

lemma sum_le_one_of_adm {p : ℕ → ℝ} (hp : Adm sp p) (s : Finset ℕ) : ∑ i ∈ s, p i ≤ 1 := by
  calc ∑ i ∈ s, p i = ∑ i ∈ s ∩ Finset.range sp.n, p i := by
        refine (Finset.sum_subset Finset.inter_subset_left (fun i hi hni => ?_)).symm
        have : ¬ i < sp.n := fun h => hni (Finset.mem_inter.mpr ⟨hi, Finset.mem_range.mpr h⟩)
        exact hp.zero i (Nat.le_of_not_lt this)
    _ ≤ ∑ i ∈ Finset.range sp.n, p i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _ => hp.nonneg i)
    _ = 1 := hp.sum1

lemma mass_nonneg {p : ℕ → ℝ} (hp : Adm sp p) (b : ℕ) : 0 ≤ mass sp p b :=
  Finset.sum_nonneg (fun i _ => hp.nonneg i)

lemma mass_le_one {p : ℕ → ℝ} (hp : Adm sp p) (b : ℕ) : mass sp p b ≤ 1 :=
  sum_le_one_of_adm hp _

lemma p_le_one {p : ℕ → ℝ} (hp : Adm sp p) (i : ℕ) : p i ≤ 1 := by
  have := sum_le_one_of_adm hp {i}
  simpa using this

lemma isInt_lt {b : ℕ} (h : sp.isInt b = true) : b < sp.nB := by
  by_contra hb
  have : sp.blk b = default := by
    simp only [Spec.blk, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hb)]
    rfl
  simp [Spec.isInt, this] at h
  exact absurd h (by decide)

lemma mass_split (h : sp.wf = true) (p : ℕ → ℝ) {b : ℕ} (hint : sp.isInt b = true) :
    mass sp p b = mass sp p (sp.blk b).c1 + mass sp p (sp.blk b).c2 := by
  have hb := isInt_lt hint
  obtain ⟨hc1, hc2, h1, h2, h3⟩ := sp.wf_int h hb hint
  have hlt1 := (sp.wf_blk h hc1).1
  have hlt2 := (sp.wf_blk h hc2).1
  unfold mass
  rw [← Finset.sum_Ico_consecutive _ (m := (sp.blk b).lo) (n := (sp.blk (sp.blk b).c1).hi)
    (k := (sp.blk b).hi) (by omega) (by omega), h1, h2, h3]

lemma mass_root (h : sp.wf = true) {p : ℕ → ℝ} (hp : Adm sp p) : mass sp p 0 = 1 := by
  obtain ⟨h1, h2⟩ := sp.wf_root h
  unfold mass
  rw [h1, h2, ← Finset.range_eq_Ico, hp.sum1]

lemma mass_leaf (h : sp.wf = true) (p : ℕ → ℝ) {i : ℕ} (hi : i < sp.n) :
    mass sp p (sp.leaf i) = p i := by
  obtain ⟨_, h1, h2⟩ := sp.wf_leaf h hi
  unfold mass
  rw [h1, h2, Nat.Ico_succ_singleton, Finset.sum_singleton]

/-- A leaf block (`hi = lo + 1`) has mass `p lo`. -/
lemma mass_of_isLeaf (p : ℕ → ℝ) {b : ℕ} (hl : sp.isLeaf b = true) :
    mass sp p b = p (sp.blk b).lo := by
  simp only [Spec.isLeaf, beq_iff_eq] at hl
  unfold mass
  rw [hl, Nat.Ico_succ_singleton, Finset.sum_singleton]

/-! ## Soundness of interval propagation -/

section Propagation

variable {p : ℕ → ℝ}

lemma low_set {L : Array ℚ} (hL : LowOK sp p L) {i : ℕ} {v : ℚ}
    (hv : i < sp.nB → (v : ℝ) ≤ mass sp p i) : LowOK sp p (L.setIfInBounds i v) := by
  intro b hb
  rw [getD_setIfInBounds]
  split_ifs with h
  · obtain ⟨rfl, _⟩ := h; exact hv hb
  · exact hL b hb

lemma up_set {U : Array ℚ} (hU : UpOK sp p U) {i : ℕ} {v : ℚ}
    (hv : i < sp.nB → mass sp p i ≤ (v : ℝ)) : UpOK sp p (U.setIfInBounds i v) := by
  intro b hb
  rw [getD_setIfInBounds]
  split_ifs with h
  · obtain ⟨rfl, _⟩ := h; exact hv hb
  · exact hU b hb

lemma sweepB_sound (h : sp.wf = true) (st : Array ℚ × Array ℚ × Bool) (b : ℕ)
    (hL : LowOK sp p st.1) (hU : UpOK sp p st.2.1) :
    LowOK sp p (sweepB sp st b).1 ∧ UpOK sp p (sweepB sp st b).2.1 := by
  unfold sweepB
  split_ifs with hint
  · have hb := isInt_lt hint
    obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int h hb hint
    have hm := mass_split h p hint
    set c1 := (sp.blk b).c1
    set c2 := (sp.blk b).c2
    have lb := hL b hb
    have ub := hU b hb
    have l1 := hL c1 hc1
    have u1 := hU c1 hc1
    have l2 := hL c2 hc2
    have u2 := hU c2 hc2
    constructor
    · refine low_set (low_set (low_set hL (fun _ => ?_)) (fun _ => ?_)) (fun _ => ?_)
      · rw [Rat.cast_max, max_le_iff]; push_cast; constructor <;> linarith
      · rw [Rat.cast_max, max_le_iff]; push_cast; constructor <;> linarith
      · rw [Rat.cast_max, max_le_iff]; push_cast; constructor <;> linarith
    · refine up_set (up_set (up_set hU (fun _ => ?_)) (fun _ => ?_)) (fun _ => ?_)
      · rw [Rat.cast_min, le_min_iff]; push_cast; constructor <;> linarith
      · rw [Rat.cast_min, le_min_iff]; push_cast; constructor <;> linarith
      · rw [Rat.cast_min, le_min_iff]; push_cast; constructor <;> linarith
  · exact ⟨hL, hU⟩

lemma foldl_sweepB_sound (h : sp.wf = true) (l : List ℕ) (st : Array ℚ × Array ℚ × Bool)
    (hL : LowOK sp p st.1) (hU : UpOK sp p st.2.1) :
    LowOK sp p (l.foldl (sweepB sp) st).1 ∧ UpOK sp p (l.foldl (sweepB sp) st).2.1 := by
  induction l generalizing st with
  | nil => exact ⟨hL, hU⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := sweepB_sound h st b hL hU
    exact ih _ h1 h2

lemma propLoop_sound (h : sp.wf = true) (k : ℕ) (L U : Array ℚ)
    (hL : LowOK sp p L) (hU : UpOK sp p U) :
    LowOK sp p (propLoop sp k L U).1 ∧ UpOK sp p (propLoop sp k L U).2 := by
  induction k generalizing L U with
  | zero => exact ⟨hL, hU⟩
  | succ k ih =>
    unfold propLoop
    have hs : LowOK sp p (sweep sp L U).1 ∧ UpOK sp p (sweep sp L U).2.1 :=
      foldl_sweepB_sound h (List.range sp.nB) (L, U, false) hL hU
    dsimp only
    split_ifs
    · exact ih _ _ hs.1 hs.2
    · exact hs

/-- Propagation never loses an admissible point. -/
theorem propagate_sound (h : sp.wf = true) (hp : Adm sp p) (L U : Array ℚ)
    (hL : LowOK sp p L) (hU : UpOK sp p U) :
    ∃ bx, propagate sp L U = some bx ∧ InBox sp p bx := by
  have hL0 : LowOK sp p (L.setIfInBounds 0 (max (L.getD 0 0) 1)) := by
    refine low_set hL (fun h0 => ?_)
    rw [Rat.cast_max, max_le_iff, mass_root h hp]
    exact ⟨by rw [← mass_root h hp]; exact hL 0 h0, by simp⟩
  have hU0 : UpOK sp p (U.setIfInBounds 0 (min (U.getD 0 0) 1)) := by
    refine up_set hU (fun h0 => ?_)
    rw [Rat.cast_min, le_min_iff, mass_root h hp]
    exact ⟨by rw [← mass_root h hp]; exact hU 0 h0, by simp⟩
  obtain ⟨h1, h2⟩ := propLoop_sound h 64 _ _ hL0 hU0
  unfold propagate
  simp only
  rw [ite_eq_left]
  · exact ⟨_, rfl, h1, h2⟩
  · rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range] at hb
    have := (h1 b hb).trans (h2 b hb)
    exact decide_eq_true (by exact_mod_cast this)

end Propagation

end Autocorr.Cert
