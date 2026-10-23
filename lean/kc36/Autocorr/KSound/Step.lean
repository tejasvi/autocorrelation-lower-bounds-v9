import Autocorr.KSound.Contrib

/-!
# Soundness of one dual step of the kernel checker

For every valid descriptor, `step` adds `packL Lp` to `rp`, `packL Ln` to `rn` and scalars to the other
accumulators, and the "validity quantity" `vq ≤ 0`:
`vq = (dap - dan)/2^124 + (Σ Lp·x - Σ Ln·x)/2^94 + (dtp - dtn)/(2n·2^64) · t`,
i.e. `y·(rhs - a·x̃) ≤ 0` for the row `a·x̃ (≤ or =) rhs` of the dual `y`.
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

variable {sp : Spec} {P : KP}

/-- Admissible point of the box, with `t` dominating all windows. -/
structure Pt (sp : Spec) (lp up : ℕ) (p : ℕ → ℝ) (t : ℝ) : Prop where
  adm : Adm sp p
  box : InBoxK sp p lp up
  t0 : 0 ≤ t
  t3 : t ≤ 3
  win : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n → 2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t

noncomputable def vq (sp : Spec) (p : ℕ → ℝ) (t : ℝ) (Lp Ln : List (ℕ × ℕ)) (dtp dtn dap dan : ℕ) : ℝ :=
  ((dap : ℝ) - dan) / 2 ^ 124 + (dotL Lp (xval sp p t) - dotL Ln (xval sp p t)) / 2 ^ 94 +
    ((dtp : ℝ) - dtn) / (2 * sp.n * 2 ^ 64) * t

/-- What a step does, abstractly. -/
def StepOK (sp : Spec) (P : KP) (lp up d : ℕ) (yn : Bool) (m : ℕ) : Prop :=
  ∃ (Lp Ln : List (ℕ × ℕ)) (dtp dtn dap dan : ℕ),
    (∀ k data rp rn tp tn ap an, step P lp up d yn m k data rp rn tp tn ap an =
        k data (rp + packL Lp) (rn + packL Ln) (tp + dtp) (tn + dtn) (ap + dap) (an + dan)) ∧
    (∀ e ∈ Lp ++ Ln, e.1 < sp.oT ∧ e.2 ≤ m * 2 ^ 36) ∧ Lp.length + Ln.length ≤ 70 ∧
    (∀ p t, Pt sp lp up p t → vq sp p t Lp Ln dtp dtn dap dan ≤ 0)

/-! ## Unpacking `kpOK` -/

structure KPFacts (sp : Spec) (P : KP) : Prop where
  wf : sp.wf = true
  n : P.n = sp.n
  nB : P.nB = sp.nB
  oZ : P.oZ = sp.oZ
  oP : P.oP = sp.oP
  oG : P.oG = sp.oG
  NC1 : P.NC1 = sp.oT
  n64 : P.n < 64
  nB128 : P.nB < 128
  NR : P.NR < 16384
  NC : sp.NC ≤ 8192
  table : tableOK sp P = true
  symP : P.symP = symRef sp true
  symN : P.symN = symRef sp false
  ints : intOK sp P = true
  canon : canonOK sp P = true

lemma kpFacts (h : kpOK sp P = true) : KPFacts sp P := by
  simp only [kpOK, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

lemma tabN_desc (sp : Spec) (P : KP) : ∀ k, (Nat.rec (motive := fun _ => Bool) true
    (fun r ih => descOK sp (desc P r) && ih) k : Bool) = true → ∀ r < k, descOK sp (desc P r) = true := by
  intro k
  induction k with
  | zero => intro _ r hr; omega
  | succ k ih =>
    intro h r hr
    have h' : descOK sp (desc P k) = true ∧ (Nat.rec (motive := fun _ => Bool) true
        (fun r ih => descOK sp (desc P r) && ih) k : Bool) = true := by
      simpa only [Bool.and_eq_true] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h'' | h''
    · exact ih h'.2 r h''
    · subst h''; exact h'.1

lemma tableOK_desc (h : tableOK sp P = true) {r : ℕ} (hr : r < P.NR) : descOK sp (desc P r) = true :=
  tabN_desc sp P P.NR h r hr

/-! ## Generic shapes -/

lemma beq_false' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

lemma beq_true' {a b : ℕ} (h : a = b) : Nat.beq a b = true := Nat.beq_eq.mpr h

lemma shl30 (m : ℕ) : Nat.shiftLeft m 30 = m * 2 ^ 30 := by rw [raw_shiftLeft, Nat.shiftLeft_eq]

lemma sel_true {α : Sort*} (a b : α) : sel true a b = a := rfl
lemma sel_false {α : Sort*} (a b : α) : sel false a b = b := rfl

lemma eqRow_eq (yn : Bool) (tgt trm : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    eqRow yn tgt trm k data rp rn tp tn ap an =
      k data (rp + sel yn tgt trm) (rn + sel yn trm tgt) (tp + 0) (tn + 0) (ap + 0) (an + 0) := by
  cases yn <;> rfl

lemma oT_lt_NC : sp.oT < sp.NC := by rw [NC_eq]; omega

/-- An equality row with +1 part `T` and −1 part `R` (both times `m·2^30`), whose identity holds. -/
lemma eqRow_stepOK {lp up d : ℕ} {yn : Bool} {m : ℕ} (T R : List (ℕ × ℕ))
    (hstep : ∀ k data rp rn tp tn ap an, step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (packL (scaleL (Nat.shiftLeft m 30) T)) (packL (scaleL (Nat.shiftLeft m 30) R)) k data rp rn tp tn ap an)
    (hcol : ∀ e ∈ T ++ R, e.1 < sp.oT ∧ e.2 ≤ 2 ^ 6) (hlen : T.length + R.length ≤ 70)
    (hid : ∀ p t, Pt sp lp up p t → dotL T (xval sp p t) = dotL R (xval sp p t)) :
    StepOK sp P lp up d yn m := by
  refine ⟨sel yn (scaleL (Nat.shiftLeft m 30) T) (scaleL (Nat.shiftLeft m 30) R),
    sel yn (scaleL (Nat.shiftLeft m 30) R) (scaleL (Nat.shiftLeft m 30) T), 0, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · intro k data rp rn tp tn ap an
    rw [hstep, eqRow_eq]; cases yn <;> rfl
  · intro e he
    have hbound : ∀ f ∈ scaleL (Nat.shiftLeft m 30) T ++ scaleL (Nat.shiftLeft m 30) R,
        f.1 < sp.oT ∧ f.2 ≤ m * 2 ^ 36 := by
      intro f hf
      simp only [scaleL, List.mem_append, List.mem_map] at hf
      rcases hf with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
      · have := hcol g (List.mem_append_left _ hg)
        refine ⟨this.1, ?_⟩
        rw [shl30]
        calc m * 2 ^ 30 * g.2 ≤ m * 2 ^ 30 * 2 ^ 6 := Nat.mul_le_mul_left _ this.2
          _ = m * 2 ^ 36 := by ring
      · have := hcol g (List.mem_append_right _ hg)
        refine ⟨this.1, ?_⟩
        rw [shl30]
        calc m * 2 ^ 30 * g.2 ≤ m * 2 ^ 30 * 2 ^ 6 := Nat.mul_le_mul_left _ this.2
          _ = m * 2 ^ 36 := by ring
    cases yn
    · exact hbound e (by simpa [sel, List.mem_append, or_comm] using he)
    · exact hbound e (by simpa [sel] using he)
  · cases yn <;> simp [sel, scaleL] <;> omega
  · intro p t hpt
    unfold vq
    have h := hid p t hpt
    cases yn <;> simp only [sel_true, sel_false, dotL_scale, h, sub_self, zero_div, add_zero,
      Nat.cast_zero, zero_mul, le_refl]

/-! ## Index bounds -/

lemma canon_lt (hw : sp.wf = true) {d e : ℕ} (hd : d < sp.nB) (he : e < sp.nB) : sp.canon d e < sp.oT := by
  unfold Spec.canon
  split_ifs with hl
  · rw [Bool.and_eq_true] at hl
    have h1 := sp.wf_blk hw hd
    have h2 := sp.wf_blk hw he
    have hle : (sp.blk d).lo < sp.n := by omega
    have hle' : (sp.blk e).lo < sp.n := by omega
    have := idx2_lt (lt_of_le_of_lt (min_le_left (sp.blk d).lo (sp.blk e).lo) hle) (max_lt hle hle')
    unfold Spec.zIdx; rw [oT_eq]; rw [oZ_eq]; omega
  · have hmin : min d e < sp.nB := lt_of_le_of_lt (min_le_left _ _) hd
    have := idx2_lt hmin (max_lt hd he)
    unfold Spec.zaIdx; rw [oT_eq, oZA_eq]; omega

/-- `rowVal` of an equality row from SoundRows is `0`. -/
lemma rowVal_zero_of_valid {row : Row} {v : ℝ} (hv : RowValid row v) (hlo : row.lo = some 0)
    (hup : row.up = some 0) : v = 0 := by
  have h1 := hv.1 0 hlo
  have h2 := hv.2 0 hup
  simp at h1 h2
  linarith

/-! ## ZA rows -/

lemma step_kind4 {lp up d : ℕ} (hk : d % 8 = 4) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (atc (Nat.shiftLeft m 30) (f13 d 0))
        (sel (dflag d)
          (Nat.add (atc (Nat.shiftLeft m 30) (f13 d 1)) (Nat.add (atc (Nat.shiftLeft m 30) (f13 d 2))
            (atc (Nat.mul 2 (Nat.shiftLeft m 30)) (f13 d 3))))
          (Nat.add (atc (Nat.shiftLeft m 30) (f13 d 1)) (atc (Nat.shiftLeft m 30) (f13 d 2))))
        k data rp rn tp tn ap an := by
  have hk' : Nat.mod d 8 = 4 := hk
  have h4 : Nat.beq (Nat.mod d 8) 4 = true := by rw [hk']; rfl
  unfold step
  simp only []
  rw [h4]
  rfl

lemma descOK_ZA {sp : Spec} {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 4) :
    keyOK sp (.ZA (kf d 0) (kf d 1) (kf d 2)) = true ∧ f13 d 0 = sp.canon (kf d 0) (kf d 1) ∧
    dflag d = decide (kf d 0 = kf d 1) ∧
    sel (Nat.beq (kf d 0) (kf d 1))
        (Nat.beq (f13 d 1) (sp.canon (sp.blk (kf d 2)).c1 (sp.blk (kf d 2)).c1) &&
          Nat.beq (f13 d 2) (sp.canon (sp.blk (kf d 2)).c2 (sp.blk (kf d 2)).c2) &&
          Nat.beq (f13 d 3) (sp.canon (sp.blk (kf d 2)).c1 (sp.blk (kf d 2)).c2))
        (Nat.beq (f13 d 1) (sp.canon (sp.blk (kf d 2)).c1 (sel (Nat.beq (kf d 2) (kf d 0)) (kf d 1) (kf d 0))) &&
          Nat.beq (f13 d 2) (sp.canon (sp.blk (kf d 2)).c2 (sel (Nat.beq (kf d 2) (kf d 0)) (kf d 1) (kf d 0))))
      = true := by
  have hk' : Nat.mod d 8 = 4 := hk
  have e0 : Nat.beq (Nat.mod d 8) 0 = false := by rw [hk']; rfl
  have e1 : Nat.beq (Nat.mod d 8) 1 = false := by rw [hk']; rfl
  have e2 : Nat.beq (Nat.mod d 8) 2 = false := by rw [hk']; rfl
  have e3 : Nat.beq (Nat.mod d 8) 3 = false := by rw [hk']; rfl
  have e4 : Nat.beq (Nat.mod d 8) 4 = true := by rw [hk']; rfl
  unfold descOK at hd
  simp only [] at hd
  rw [e0, sel_false, e1, sel_false, e2, sel_false, e3, sel_false, e4, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hd
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hd
  exact ⟨h1, h2, by simpa using h3, h4⟩

theorem stepOK_ZA (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 4)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hflag, hrest⟩ := descOK_ZA hd hk
  generalize kf d 0 = a at hkey hf0 hflag hrest
  generalize kf d 1 = b at hkey hf0 hflag hrest
  generalize kf d 2 = s at hkey hf0 hflag hrest
  have hkey' := hkey
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hkey'
  obtain ⟨⟨⟨⟨ha, hb⟩, hs⟩, hsab⟩, hint⟩ := hkey'
  obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int hkp.wf hs hint
  have hrow : ∀ p t, Pt sp lp up p t →
      rowVal (rowOf sp default (.ZA a b s)).ent (xval sp p t) = 0 := fun p t _ =>
    rowVal_zero_of_valid (valid_ZA (bx := default) hkp.wf hkey) rfl rfl
  by_cases hab : a = b
  · -- diagonal
    have hfl : dflag d = true := by rw [hflag]; simp [hab]
    rw [beq_true' hab, sel_true] at hrest
    simp only [Bool.and_eq_true, Nat.beq_eq] at hrest
    obtain ⟨⟨h1, h2⟩, h3⟩ := hrest
    refine eqRow_stepOK [(f13 d 0, 1)] [(f13 d 1, 1), (f13 d 2, 1), (f13 d 3, 2)] ?_ ?_ ?_ ?_
    · intro k data rp rn tp tn ap an
      rw [step_kind4 hk, hfl, sel_true]
      congr 1
      · rw [atc_eq]; simp only [packL, scaleL, List.map_cons, List.map_nil, mul_one]
      · rw [atc_eq, atc_eq, atc_eq, raw_add, raw_add, raw_mul]
        simp only [packL, scaleL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one]
        ring
    · intro e he
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · exact ⟨hf0 ▸ canon_lt hkp.wf ha hb, by norm_num⟩
      · exact ⟨h1 ▸ canon_lt hkp.wf hc1 hc1, by norm_num⟩
      · exact ⟨h2 ▸ canon_lt hkp.wf hc2 hc2, by norm_num⟩
      · exact ⟨h3 ▸ canon_lt hkp.wf hc1 hc2, by norm_num⟩
    · simp
    · intro p t hpt
      have hr := hrow p t hpt
      simp only [rowOf, if_pos hab, rowVal_cons, rowVal_nil] at hr
      simp only [dotL_cons, dotL_nil, hf0, h1, h2, h3]
      push_cast at hr ⊢
      linarith
  · -- off-diagonal
    have hfl : dflag d = false := by rw [hflag]; simp [hab]
    rw [beq_false' hab, sel_false] at hrest
    simp only [Bool.and_eq_true, Nat.beq_eq] at hrest
    obtain ⟨h1, h2⟩ := hrest
    have ho : sel (Nat.beq s a) b a = if s = a then b else a := by
      by_cases hsa : s = a
      · rw [if_pos hsa, beq_true' hsa]; rfl
      · rw [if_neg hsa, beq_false' hsa]; rfl
    rw [ho] at h1 h2
    have hoB : (if s = a then b else a) < sp.nB := by split_ifs <;> assumption
    refine eqRow_stepOK [(f13 d 0, 1)] [(f13 d 1, 1), (f13 d 2, 1)] ?_ ?_ ?_ ?_
    · intro k data rp rn tp tn ap an
      rw [step_kind4 hk, hfl, sel_false]
      congr 1
      · rw [atc_eq]; simp only [packL, scaleL, List.map_cons, List.map_nil, mul_one]
      · rw [atc_eq, atc_eq, raw_add]
        simp only [packL, scaleL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
    · intro e he
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨hf0 ▸ canon_lt hkp.wf ha hb, by norm_num⟩
      · exact ⟨h1 ▸ canon_lt hkp.wf hc1 hoB, by norm_num⟩
      · exact ⟨h2 ▸ canon_lt hkp.wf hc2 hoB, by norm_num⟩
    · simp
    · intro p t hpt
      have hr := hrow p t hpt
      simp only [rowOf, if_neg hab, rowVal_cons, rowVal_nil] at hr
      simp only [dotL_cons, dotL_nil, hf0, h1, h2]
      push_cast at hr ⊢
      linarith

/-! ## Dispatch lemmas -/

lemma beqk {d : ℕ} {K : ℕ} (hk : d % 8 = K) (j : ℕ) : Nat.beq (Nat.mod d 8) j = Nat.beq K j := by
  rw [show Nat.mod d 8 = d % 8 from rfl, hk]

lemma beqF {d K : ℕ} (hk : d % 8 = K) (j : ℕ) (h : K ≠ j) : Nat.beq (Nat.mod d 8) j = false := by
  rw [show Nat.mod d 8 = d % 8 from rfl, hk]; exact beq_false' h

lemma beqT {d K : ℕ} (hk : d % 8 = K) : Nat.beq (Nat.mod d 8) K = true := by
  rw [show Nat.mod d 8 = d % 8 from rfl, hk]; exact beq_true' rfl

lemma zIdxK_eq (hkp : KPFacts sp P) (i j : ℕ) : zIdxK P.oZ P.n i j = sp.zIdx i j := by
  unfold zIdxK Spec.zIdx
  rw [hkp.oZ, hkp.n]
  by_cases h : i ≤ j
  · rw [ble_true h, sel_true, min_eq_left h, max_eq_right h, raw_add, raw_add, raw_mul]; ring
  · rw [ble_false h, sel_false, min_eq_right (by omega), max_eq_left (by omega), raw_add, raw_add,
      raw_mul]; ring

lemma patPL_length (oZ n c k : ℕ) : (patPL oZ n c k).length ≤ k := by
  induction k with
  | zero => simp [patPL]
  | succ k ih => simp only [patPL, List.length_append]; split_ifs <;> simp <;> omega

lemma patRL_length (oZ n i k : ℕ) : (patRL oZ n i k).length = k := by
  induction k with
  | zero => simp [patRL]
  | succ k ih => simp [patRL, ih]

lemma patPL_mem {oZ n c k : ℕ} {e : ℕ × ℕ} (he : e ∈ patPL oZ n c k) :
    ∃ i < k, i ≤ c ∧ c - i < n ∧ e = (zIdxK oZ n i (c - i), 1) := by
  induction k with
  | zero => simp [patPL] at he
  | succ k ih =>
    simp only [patPL, List.mem_append] at he
    rcases he with h | h
    · split_ifs at h with hc
      · simp only [List.mem_singleton] at h; exact ⟨k, by omega, hc.1, hc.2, h⟩
      · simp at h
    · obtain ⟨i, hi, h1, h2, h3⟩ := ih h; exact ⟨i, by omega, h1, h2, h3⟩

lemma patRL_mem {oZ n i k : ℕ} {e : ℕ × ℕ} (he : e ∈ patRL oZ n i k) :
    ∃ j < k, e = (zIdxK oZ n i j, 1) := by
  induction k with
  | zero => simp [patRL] at he
  | succ k ih =>
    simp only [patRL, List.mem_cons] at he
    rcases he with h | h
    · exact ⟨k, by omega, h⟩
    · obtain ⟨j, hj, h'⟩ := ih h; exact ⟨j, by omega, h'⟩

lemma dotL_patPL (oZ n c : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    dotL (patPL oZ n c k) x = ∑ i ∈ Finset.range k,
      (if i ≤ c ∧ c - i < n then x (zIdxK oZ n i (c - i)) else 0) := by
  induction k with
  | zero => simp [patPL]
  | succ k ih =>
    rw [patPL, dotL_append, ih, Finset.sum_range_succ, add_comm]
    split_ifs <;> simp

lemma dotL_patRL (oZ n i : ℕ) (x : ℕ → ℝ) (k : ℕ) :
    dotL (patRL oZ n i k) x = ∑ j ∈ Finset.range k, x (zIdxK oZ n i j) := by
  induction k with
  | zero => simp [patRL]
  | succ k ih => rw [patRL, dotL_cons, ih, Finset.sum_range_succ]; push_cast; ring

lemma zIdx_lt_oT {i j : ℕ} (hi : i < sp.n) (hj : j < sp.n) : sp.zIdx i j < sp.oT := by
  have hmin : min i j < sp.n := lt_of_le_of_lt (min_le_left _ _) hi
  have := idx2_lt hmin (max_lt hi hj)
  unfold Spec.zIdx; rw [oT_eq, oZ_eq]; omega

/-! ## P rows -/

lemma step_kind1 {lp up d : ℕ} (hk : d % 8 = 1) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (atc (Nat.shiftLeft m 30) (f13 d 0))
        (Nat.mul (Nat.shiftLeft m 30) (patP P.oZ P.n (f13 d 1))) k data rp rn tp tn ap an := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1]
  rfl

lemma descOK_P {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 1) :
    keyOK sp (.P (kf d 0)) = true ∧ f13 d 0 = sp.oP + kf d 0 ∧ f13 d 1 = kf d 0 := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqF hk 0 (by decide), sel_false, beqT hk, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq] at hd
  exact ⟨hd.1.1, hd.1.2, hd.2⟩

theorem stepOK_P (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 1)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hf1⟩ := descOK_P hd hk
  generalize kf d 0 = c at hkey hf0 hf1
  have hc : c + 2 ≤ 2 * sp.n := by simpa [keyOK] using hkey
  refine eqRow_stepOK [(f13 d 0, 1)] (patPL P.oZ P.n c P.n) ?_ ?_ ?_ ?_
  · intro k data rp rn tp tn ap an
    rw [step_kind1 hk, hf1, patP_eq, raw_mul, ← packL_scale, atc_eq]
    simp only [packL, scaleL, List.map_cons, List.map_nil, mul_one]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [List.mem_singleton] at he; subst he
      refine ⟨?_, by norm_num⟩
      rw [hf0, oT_eq, oP_eq]; omega
    · obtain ⟨i, hi, h1, h2, rfl⟩ := patPL_mem he
      rw [hkp.n] at hi h2
      refine ⟨?_, by norm_num⟩
      rw [zIdxK_eq hkp]; exact zIdx_lt_oT hi h2
  · have := patPL_length P.oZ P.n c P.n
    have h64 := hkp.n64
    simp only [List.length_singleton]; omega
  · intro p t hpt
    rw [dotL_patPL, hf0, dotL_cons, dotL_nil, Nat.cast_one, one_mul, add_zero, xval_P hc, Pc_eq]
    simp only [zIdxK_eq hkp]
    rw [hkp.n]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    split_ifs with h
    · rw [xval_z hi h.2]
    · rfl

/-! ## G rows -/

lemma step_kind2 {lp up d : ℕ} (hk : d % 8 = 2) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (atc (Nat.shiftLeft m 30) (f13 d 0))
        (Nat.add (atc (Nat.shiftLeft m 30) (f13 d 1)) (sel (dflag d) (atc (Nat.shiftLeft m 30) (f13 d 2)) 0))
        k data rp rn tp tn ap an := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1, beqk hk 2]
  rfl

lemma descOK_G {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 2) :
    keyOK sp (.G (kf d 0)) = true ∧ f13 d 0 = sp.oG + kf d 0 ∧ f13 d 1 = sp.oP + kf d 0 ∧
    dflag d = decide (0 < kf d 0) ∧ (kf d 0 = 0 ∨ f13 d 2 = sp.oG + (kf d 0 - 1)) := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqF hk 0 (by decide), sel_false, beqF hk 1 (by decide), sel_false, beqT hk, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Bool.or_eq_true] at hd
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hd
  exact ⟨h1, h2, h3, h4, h5⟩

theorem stepOK_G (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 2)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hf1, hflag, hf2⟩ := descOK_G hd hk
  generalize kf d 0 = c at hkey hf0 hf1 hflag hf2
  have hc : c + 2 ≤ 2 * sp.n := by simpa [keyOK] using hkey
  by_cases hc0 : c = 0
  · subst hc0
    have hfl : dflag d = false := by rw [hflag]; simp
    refine eqRow_stepOK [(f13 d 0, 1)] [(f13 d 1, 1)] ?_ ?_ ?_ ?_
    · intro k data rp rn tp tn ap an
      rw [step_kind2 hk, hfl, sel_false, atc_eq, atc_eq, raw_add]
      simp only [packL, scaleL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
    · intro e he
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨by rw [hf0, oT_eq, oG_eq]; omega, by norm_num⟩
      · exact ⟨by rw [hf1, oT_eq, oP_eq]; omega, by norm_num⟩
    · simp
    · intro p t hpt
      simp only [dotL_cons, dotL_nil, hf0, hf1, Nat.cast_one, one_mul, add_zero]
      have hG0 := xval_G (sp := sp) (p := p) (t := t) (c := 0) hc
      have hP0 := xval_P (sp := sp) (p := p) (t := t) (c := 0) hc
      rw [add_zero] at hG0 hP0
      rw [hG0, hP0, Gc_zero]
  · have hfl : dflag d = true := by rw [hflag]; simp; omega
    have hf2' : f13 d 2 = sp.oG + (c - 1) := hf2.resolve_left hc0
    refine eqRow_stepOK [(f13 d 0, 1)] [(f13 d 1, 1), (f13 d 2, 1)] ?_ ?_ ?_ ?_
    · intro k data rp rn tp tn ap an
      rw [step_kind2 hk, hfl, sel_true, atc_eq, atc_eq, atc_eq, raw_add]
      simp only [packL, scaleL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
    · intro e he
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨by rw [hf0, oT_eq, oG_eq]; omega, by norm_num⟩
      · exact ⟨by rw [hf1, oT_eq, oP_eq]; omega, by norm_num⟩
      · exact ⟨by rw [hf2', oT_eq, oG_eq]; omega, by norm_num⟩
    · simp
    · intro p t hpt
      simp only [dotL_cons, dotL_nil, hf0, hf1, hf2', Nat.cast_one, one_mul, add_zero]
      rw [xval_G hc, xval_P hc, xval_G (by omega)]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [Gc_succ, show c' + 1 - 1 = c' by omega]

/-! ## tree rows -/

lemma step_kind3 {lp up d : ℕ} (hk : d % 8 = 3) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (atc (Nat.shiftLeft m 30) (f13 d 0))
        (Nat.add (atc (Nat.shiftLeft m 30) (f13 d 1)) (atc (Nat.shiftLeft m 30) (f13 d 2)))
        k data rp rn tp tn ap an := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1, beqk hk 2, beqk hk 3]
  rfl

lemma descOK_tree {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 3) :
    keyOK sp (.tree (kf d 0)) = true ∧ f13 d 0 = kf d 0 ∧ f13 d 1 = (sp.blk (kf d 0)).c1 ∧
    f13 d 2 = (sp.blk (kf d 0)).c2 := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqF hk 0 (by decide), sel_false, beqF hk 1 (by decide), sel_false, beqF hk 2 (by decide), sel_false, beqT hk, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq] at hd
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hd
  exact ⟨h1, h2, h3, h4⟩

theorem stepOK_tree (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 3)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hf1, hf2⟩ := descOK_tree hd hk
  generalize kf d 0 = b at hkey hf0 hf1 hf2
  have hkey' := hkey
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq] at hkey'
  obtain ⟨hb, hint⟩ := hkey'
  obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int hkp.wf hb hint
  refine eqRow_stepOK [(f13 d 0, 1)] [(f13 d 1, 1), (f13 d 2, 1)] ?_ ?_ ?_ ?_
  · intro k data rp rn tp tn ap an
    rw [step_kind3 hk, atc_eq, atc_eq, atc_eq, raw_add]
    simp only [packL, scaleL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
  · have hnb : sp.nB ≤ sp.oT := by rw [oT_eq]; omega
    intro e he
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨by rw [hf0]; omega, by norm_num⟩
    · exact ⟨by rw [hf1]; omega, by norm_num⟩
    · exact ⟨by rw [hf2]; omega, by norm_num⟩
  · simp
  · intro p t hpt
    simp only [dotL_cons, dotL_nil, hf0, hf1, hf2, Nat.cast_one, one_mul, add_zero]
    rw [xval_m hb, xval_m hc1, xval_m hc2, mass_split hkp.wf p hint]

/-! ## rlt rows -/

lemma step_kind5 {lp up d : ℕ} (hk : d % 8 = 5) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      eqRow yn (Nat.mul (Nat.shiftLeft m 30) (patR P.oZ P.n (f13 d 0)))
        (atc (Nat.shiftLeft m 30) (f13 d 1)) k data rp rn tp tn ap an := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1, beqk hk 2, beqk hk 3, beqk hk 5]
  rfl

lemma descOK_rlt {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 5) :
    keyOK sp (.rlt (kf d 0)) = true ∧ f13 d 0 = kf d 0 ∧ f13 d 1 = sp.leaf (kf d 0) := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqF hk 0 (by decide), sel_false, beqF hk 1 (by decide), sel_false, beqF hk 2 (by decide), sel_false, beqF hk 3 (by decide), sel_false,
    beqF hk 4 (by decide), sel_false, beqT hk, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq] at hd
  exact ⟨hd.1.1, hd.1.2, hd.2⟩

theorem stepOK_rlt (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 5)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hf1⟩ := descOK_rlt hd hk
  generalize kf d 0 = i at hkey hf0 hf1
  have hi : i < sp.n := by simpa [keyOK] using hkey
  obtain ⟨hl, -, -⟩ := sp.wf_leaf hkp.wf hi
  refine eqRow_stepOK (patRL P.oZ P.n i P.n) [(f13 d 1, 1)] ?_ ?_ ?_ ?_
  · intro k data rp rn tp tn ap an
    rw [step_kind5 hk, hf0, patR_eq, raw_mul, ← packL_scale, atc_eq]
    simp only [packL, scaleL, List.map_cons, List.map_nil, mul_one]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨j, hj, rfl⟩ := patRL_mem he
      rw [hkp.n] at hj
      refine ⟨?_, by norm_num⟩
      rw [zIdxK_eq hkp]; exact zIdx_lt_oT hi hj
    · simp only [List.mem_singleton] at he; subst he
      refine ⟨?_, by norm_num⟩
      rw [hf1]; have : sp.nB ≤ sp.oT := by rw [oT_eq]; omega
      omega
  · rw [patRL_length]; have := hkp.n64; simp; omega
  · intro p t hpt
    rw [dotL_patRL, hf1, dotL_cons, dotL_nil, Nat.cast_one, one_mul, add_zero, xval_m hl,
      mass_leaf hkp.wf p hi]
    simp only [zIdxK_eq hkp]
    rw [hkp.n]
    have : ∀ j ∈ Finset.range sp.n, xval sp p t (sp.zIdx i j) = p i * p j := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [xval_z hi hj]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hpt.adm.sum1, mul_one]

/-! ## Window rows (rescaled: `G_c2 - G_{c1-1} - (k/2n) t ≤ 0`) -/

lemma step_kind0 {lp up d : ℕ} (hk : d % 8 = 0) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      sel yn (k data (Nat.add rp (atc (Nat.shiftLeft m 30) (f13 d 0)))
        (Nat.add rn (sel (dflag d) (atc (Nat.shiftLeft m 30) (f13 d 1)) 0)) tp
        (Nat.add tn (Nat.mul m (f13 d 2))) ap an) (k data rp rn tp tn ap an) := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1, beqk hk 2, beqk hk 3, beqk hk 5, beqk hk 0]
  rfl

lemma descOK_win {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 0) :
    keyOK sp (.win (kf d 0) (kf d 1)) = true ∧ f13 d 0 = sp.oG + kf d 1 ∧ dflag d = decide (0 < kf d 0) ∧
    (kf d 0 = 0 ∨ f13 d 1 = sp.oG + (kf d 0 - 1)) ∧ f13 d 2 = kf d 1 - kf d 0 + 2 := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqT hk, sel_true] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Bool.or_eq_true] at hd
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hd
  exact ⟨h1, h2, h3, h4, h5⟩

lemma noop_stepOK {lp up d : ℕ} {yn : Bool} {m : ℕ}
    (h : ∀ k data rp rn tp tn ap an, step P lp up d yn m k data rp rn tp tn ap an = k data rp rn tp tn ap an) :
    StepOK sp P lp up d yn m := by
  refine ⟨[], [], 0, 0, 0, 0, fun k data rp rn tp tn ap an => by rw [h]; simp, by simp, by simp,
    fun p t _ => by simp [vq]⟩

lemma cast_shl30 (m : ℕ) : ((Nat.shiftLeft m 30 : ℕ) : ℝ) = (m : ℝ) * 2 ^ 30 := by
  rw [shl30]; push_cast; ring

lemma win_ineq {m W k N t : ℝ} (hm : 0 ≤ m) (hk : 0 < k) (hN : 0 < N) (hw : N / k * W ≤ t) :
    m * 2 ^ 30 * W / 2 ^ 94 + -(m * k) / (N * 2 ^ 64) * t ≤ 0 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hk] at hw
  have e : m * 2 ^ 30 * W / 2 ^ 94 + -(m * k) / (N * 2 ^ 64) * t = m * (N * W - t * k) / (N * 2 ^ 64) := by
    field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  exact mul_nonpos_of_nonneg_of_nonpos hm (by linarith)

theorem stepOK_win (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 0)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  obtain ⟨hkey, hf0, hflag, hf1, hf2⟩ := descOK_win hd hk
  generalize kf d 0 = c1 at hkey hf0 hflag hf1 hf2
  generalize kf d 1 = c2 at hkey hf0 hflag hf1 hf2
  have hk' : c1 ≤ c2 ∧ c2 + 2 ≤ 2 * sp.n := by simpa [keyOK] using hkey
  cases yn
  · exact noop_stepOK (fun k data rp rn tp tn ap an => by rw [step_kind0 hk]; rfl)
  have hoT : sp.oG + c2 < sp.oT := by rw [oT_eq, oG_eq]; omega
  have hn : (0 : ℝ) < 2 * sp.n := by have := sp.wf_n_pos hkp.wf; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hc12 : (c1 : ℝ) ≤ c2 := by exact_mod_cast hk'.1
  have hk0 : (0 : ℝ) < (c2 : ℝ) - c1 + 2 := by linarith
  have hkc : ((f13 d 2 : ℕ) : ℝ) = (c2 : ℝ) - c1 + 2 := by
    rw [hf2, Nat.cast_add, Nat.cast_sub hk'.1]; push_cast; ring
  by_cases hc1 : c1 = 0
  · subst hc1
    have hfl : dflag d = false := by rw [hflag]; simp
    refine ⟨[(f13 d 0, Nat.shiftLeft m 30)], [], 0, m * f13 d 2, 0, 0, ?_, ?_, by simp, ?_⟩
    · intro k data rp rn tp tn ap an
      rw [step_kind0 hk, sel_true, hfl, sel_false, atc_eq, raw_add, raw_add, raw_add, raw_mul]
      simp [packL]
    · intro e he
      simp only [List.append_nil, List.mem_singleton] at he; subst he
      exact ⟨hf0 ▸ hoT, by rw [shl30]; exact Nat.mul_le_mul_left _ (by norm_num)⟩
    · intro p t hpt
      have hw := hpt.win 0 c2 (Nat.zero_le _) hk'.2
      rw [wsum_eq_Gc_zero] at hw
      unfold vq
      simp only [dotL_cons, dotL_nil, add_zero, hf0, cast_shl30, Nat.cast_zero, sub_zero, zero_sub,
        zero_div, zero_add, Nat.cast_mul, hkc]
      rw [xval_G hk'.2]
      exact win_ineq hm (by positivity) hn (by simpa using hw)
  · have hfl : dflag d = true := by rw [hflag]; simp; omega
    have hf1' := hf1.resolve_left hc1
    refine ⟨[(f13 d 0, Nat.shiftLeft m 30)], [(f13 d 1, Nat.shiftLeft m 30)], 0, m * f13 d 2, 0, 0,
      ?_, ?_, by simp, ?_⟩
    · intro k data rp rn tp tn ap an
      rw [step_kind0 hk, sel_true, hfl, sel_true, atc_eq, atc_eq, raw_add, raw_add, raw_add, raw_mul]
      simp [packL]
    · intro e he
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨hf0 ▸ hoT, by rw [shl30]; exact Nat.mul_le_mul_left _ (by norm_num)⟩
      · refine ⟨by rw [hf1', oT_eq, oG_eq]; omega, by rw [shl30]; exact Nat.mul_le_mul_left _ (by norm_num)⟩
    · intro p t hpt
      have hw := hpt.win c1 c2 hk'.1 hk'.2
      rw [wsum_eq_Gc_sub (by omega) hk'.1] at hw
      unfold vq
      simp only [dotL_cons, dotL_nil, add_zero, hf0, hf1', cast_shl30, Nat.cast_zero, sub_zero, zero_sub,
        zero_div, zero_add, Nat.cast_mul, hkc]
      rw [xval_G hk'.2, xval_G (by omega)]
      rw [show ((m : ℝ) * 2 ^ 30 * Gc sp p c2 - m * 2 ^ 30 * Gc sp p (c1 - 1)) / 2 ^ 94 =
        m * 2 ^ 30 * (Gc sp p c2 - Gc sp p (c1 - 1)) / 2 ^ 94 by ring]
      exact win_ineq hm hk0 hn hw

/-! ## The sym row -/

noncomputable def symL (sp : Spec) (pos : Bool) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | i + 1 =>
    (if pos then (if sp.n ≤ 2 * i then [(sp.leaf i, Nat.shiftLeft (2 * i - (sp.n - 1)) 30)] else [])
     else (if 2 * i + 2 ≤ sp.n then [(sp.leaf i, Nat.shiftLeft (sp.n - 1 - 2 * i) 30)] else [])) ++ symL sp pos i

lemma symRef_eq' (sp : Spec) (pos : Bool) : ∀ k, (Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc
      (sel pos
        (sel (Nat.ble sp.n (Nat.mul 2 i))
          (atc (Nat.shiftLeft (Nat.sub (Nat.mul 2 i) (Nat.sub sp.n 1)) 30) (sp.leaf i)) 0)
        (sel (Nat.ble (Nat.add (Nat.mul 2 i) 2) sp.n)
          (atc (Nat.shiftLeft (Nat.sub (Nat.sub sp.n 1) (Nat.mul 2 i)) 30) (sp.leaf i)) 0))) k : ℕ)
    = packL (symL sp pos k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show Nat.add _ _ = _
    rw [ih, symL, packL_append, raw_add, add_comm]
    congr 1
    cases pos
    · by_cases h : 2 * k + 2 ≤ sp.n
      · rw [sel_false, ble_true (show Nat.add (Nat.mul 2 k) 2 ≤ sp.n from h), sel_true, atc_eq]
        simp [h, raw_sub, raw_mul]
      · rw [sel_false, ble_false (show ¬ Nat.add (Nat.mul 2 k) 2 ≤ sp.n from h), sel_false]
        simp [h]
    · by_cases h : sp.n ≤ 2 * k
      · rw [sel_true, ble_true (show sp.n ≤ Nat.mul 2 k from h), sel_true, atc_eq]
        simp [h, raw_sub, raw_mul]
      · rw [sel_true, ble_false (show ¬ sp.n ≤ Nat.mul 2 k from h), sel_false]
        simp [h]

lemma symRef_eq (sp : Spec) (pos : Bool) : symRef sp pos = packL (symL sp pos sp.n) := symRef_eq' sp pos sp.n

lemma symL_mem {sp : Spec} {pos : Bool} {k : ℕ} (hk : k ≤ sp.n) {e : ℕ × ℕ} (he : e ∈ symL sp pos k) :
    ∃ i < k, e.1 = sp.leaf i ∧ e.2 ≤ sp.n * 2 ^ 30 := by
  induction k with
  | zero => simp [symL] at he
  | succ k ih =>
    simp only [symL, List.mem_append] at he
    rcases he with h | h
    · refine ⟨k, by omega, ?_⟩
      cases pos
      · by_cases hc : 2 * k + 2 ≤ sp.n
        · rw [if_neg (by simp), if_pos hc, List.mem_singleton] at h
          rw [h, shl30]; exact ⟨rfl, Nat.mul_le_mul_right _ (by omega)⟩
        · rw [if_neg (by simp), if_neg hc] at h; simp at h
      · by_cases hc : sp.n ≤ 2 * k
        · rw [if_pos rfl, if_pos hc, List.mem_singleton] at h
          rw [h, shl30]; exact ⟨rfl, Nat.mul_le_mul_right _ (by omega)⟩
        · rw [if_pos rfl, if_neg hc] at h; simp at h
    · obtain ⟨i, hi, h1, h2⟩ := ih (by omega) h; exact ⟨i, by omega, h1, h2⟩

lemma symL_length (sp : Spec) (k : ℕ) : (symL sp true k).length + (symL sp false k).length ≤ k := by
  induction k with
  | zero => simp [symL]
  | succ k ih =>
    simp only [symL, List.length_append, ite_true, Bool.false_eq_true, ite_false]
    by_cases h1 : sp.n ≤ 2 * k
    · have h2 : ¬ 2 * k + 2 ≤ sp.n := by omega
      rw [if_pos h1, if_neg h2]; simp only [List.length_singleton, List.length_nil]; omega
    · by_cases h2 : 2 * k + 2 ≤ sp.n
      · rw [if_neg h1, if_pos h2]; simp only [List.length_singleton, List.length_nil]; omega
      · rw [if_neg h1, if_neg h2]; simp only [List.length_nil]; omega

lemma dotL_symL (sp : Spec) (hn : 1 ≤ sp.n) (x : ℕ → ℝ) (k : ℕ) :
    dotL (symL sp true k) x - dotL (symL sp false k) x =
      ∑ i ∈ Finset.range k, (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * 2 ^ 30 * x (sp.leaf i) := by
  induction k with
  | zero => simp [symL]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [symL, dotL_append, Bool.false_eq_true, ite_true, ite_false]
    by_cases h1 : sp.n ≤ 2 * k
    · have h2 : ¬ 2 * k + 2 ≤ sp.n := by omega
      rw [if_pos h1, if_neg h2]
      simp only [dotL_cons, dotL_nil, cast_shl30]
      rw [Nat.cast_sub (show sp.n - 1 ≤ 2 * k by omega), Nat.cast_sub (show 1 ≤ sp.n by omega)]
      push_cast; ring
    · by_cases h2 : 2 * k + 2 ≤ sp.n
      · rw [if_neg h1, if_pos h2]
        simp only [dotL_cons, dotL_nil, cast_shl30]
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast; ring
      · rw [if_neg h1, if_neg h2]
        have : (2 * (k : ℝ) - ((sp.n : ℝ) - 1)) = 0 := by
          have : sp.n = 2 * k + 1 := by omega
          rw [this]; push_cast; ring
        simp [this]

lemma step_kind6 {lp up d : ℕ} (hk : d % 8 = 6) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      sel yn (k data (Nat.add rp (Nat.mul m P.symP)) (Nat.add rn (Nat.mul m P.symN)) tp tn ap an)
        (k data rp rn tp tn ap an) := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7, beqk hk 1, beqk hk 2, beqk hk 3, beqk hk 5, beqk hk 0]
  rfl

theorem stepOK_sym (hkp : KPFacts sp P) {lp up d : ℕ} (hk : d % 8 = 6) (yn : Bool) (m : ℕ) :
    StepOK sp P lp up d yn m := by
  cases yn
  · exact noop_stepOK (fun k data rp rn tp tn ap an => by rw [step_kind6 hk]; rfl)
  refine ⟨scaleL m (symL sp true sp.n), scaleL m (symL sp false sp.n), 0, 0, 0, 0, ?_, ?_, ?_, ?_⟩
  · intro k data rp rn tp tn ap an
    rw [step_kind6 hk, sel_true, hkp.symP, hkp.symN, symRef_eq, symRef_eq, raw_add, raw_add, raw_mul,
      raw_mul, packL_scale, packL_scale]
    simp
  · have h64 := hkp.n64
    rw [hkp.n] at h64
    have hnb : sp.nB ≤ sp.oT := by rw [oT_eq]; omega
    intro e he
    simp only [scaleL, List.mem_append, List.mem_map] at he
    rcases he with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ <;>
    · obtain ⟨i, hi, h1, h2⟩ := symL_mem le_rfl hf
      refine ⟨by rw [h1]; have := (sp.wf_leaf hkp.wf hi).1; omega, ?_⟩
      calc m * f.2 ≤ m * (sp.n * 2 ^ 30) := Nat.mul_le_mul_left _ h2
        _ ≤ m * 2 ^ 36 := by
          apply Nat.mul_le_mul_left
          calc sp.n * 2 ^ 30 ≤ 2 ^ 6 * 2 ^ 30 := Nat.mul_le_mul_right _ (by omega)
            _ = 2 ^ 36 := by norm_num
  · have := symL_length sp sp.n; have h64 := hkp.n64; rw [hkp.n] at h64
    simp only [scaleL, List.length_map]; omega
  · intro p t hpt
    unfold vq
    rw [dotL_scale, dotL_scale, ← mul_sub, dotL_symL sp (sp.wf_n_pos hkp.wf)]
    have : ∑ i ∈ Finset.range sp.n, (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * 2 ^ 30 * xval sp p t (sp.leaf i) =
        2 ^ 30 * ∑ i ∈ Finset.range sp.n, (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * p i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [xval_m (sp.wf_leaf hkp.wf hi).1, mass_leaf hkp.wf p hi]; ring
    rw [this]
    have hh := hpt.adm.half
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    simp only [Nat.cast_zero, sub_zero, zero_div, zero_add, zero_mul, add_zero]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos hm (mul_nonpos_of_nonneg_of_nonpos (by positivity) hh)

/-! ## McCormick rows -/

section McCormick
variable {m ld ud le ue D E : ℝ}

lemma mc0 (hm : 0 ≤ m) (hD : ld / 2 ^ 30 ≤ D) (hE : le / 2 ^ 30 ≤ E) :
    (0 - m * (ld * le)) / 2 ^ 124 + (m * le * D + m * ld * E - m * 2 ^ 30 * (D * E)) / 2 ^ 94 ≤ 0 := by
  rw [div_le_iff₀ (by positivity)] at hD hE
  have e : (0 - m * (ld * le)) / 2 ^ 124 + (m * le * D + m * ld * E - m * 2 ^ 30 * (D * E)) / 2 ^ 94 =
      -(m * (D * 2 ^ 30 - ld) * (E * 2 ^ 30 - le)) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)) (by positivity)

lemma mc1 (hm : 0 ≤ m) (hD : D ≤ ud / 2 ^ 30) (hE : E ≤ ue / 2 ^ 30) :
    (0 - m * (ud * ue)) / 2 ^ 124 + (m * ue * D + m * ud * E - m * 2 ^ 30 * (D * E)) / 2 ^ 94 ≤ 0 := by
  rw [le_div_iff₀ (by positivity)] at hD hE
  have e : (0 - m * (ud * ue)) / 2 ^ 124 + (m * ue * D + m * ud * E - m * 2 ^ 30 * (D * E)) / 2 ^ 94 =
      -(m * (ud - D * 2 ^ 30) * (ue - E * 2 ^ 30)) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)) (by positivity)

lemma mc2 (hm : 0 ≤ m) (hD : ld / 2 ^ 30 ≤ D) (hE : E ≤ ue / 2 ^ 30) :
    (m * (ld * ue) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * E) - (m * ue * D + m * ld * E)) / 2 ^ 94 ≤ 0 := by
  rw [div_le_iff₀ (by positivity)] at hD
  rw [le_div_iff₀ (by positivity)] at hE
  have e : (m * (ld * ue) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * E) - (m * ue * D + m * ld * E)) / 2 ^ 94 =
      -(m * (D * 2 ^ 30 - ld) * (ue - E * 2 ^ 30)) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)) (by positivity)

lemma mc3 (hm : 0 ≤ m) (hD : D ≤ ud / 2 ^ 30) (hE : le / 2 ^ 30 ≤ E) :
    (m * (ud * le) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * E) - (m * le * D + m * ud * E)) / 2 ^ 94 ≤ 0 := by
  rw [le_div_iff₀ (by positivity)] at hD
  rw [div_le_iff₀ (by positivity)] at hE
  have e : (m * (ud * le) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * E) - (m * le * D + m * ud * E)) / 2 ^ 94 =
      -(m * (ud - D * 2 ^ 30) * (E * 2 ^ 30 - le)) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)) (by positivity)

lemma mcd0 (hm : 0 ≤ m) :
    (0 - m * (ld * ld)) / 2 ^ 124 + (m * (2 * ld) * D - m * 2 ^ 30 * (D * D)) / 2 ^ 94 ≤ 0 := by
  have e : (0 - m * (ld * ld)) / 2 ^ 124 + (m * (2 * ld) * D - m * 2 ^ 30 * (D * D)) / 2 ^ 94 =
      -(m * (D * 2 ^ 30 - ld) ^ 2) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg hm (sq_nonneg _)) (by positivity)

lemma mcd2 (hm : 0 ≤ m) (hD1 : ld / 2 ^ 30 ≤ D) (hD2 : D ≤ ud / 2 ^ 30) :
    (m * (ld * ud) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * D) - m * (ld + ud) * D) / 2 ^ 94 ≤ 0 := by
  rw [div_le_iff₀ (by positivity)] at hD1
  rw [le_div_iff₀ (by positivity)] at hD2
  have e : (m * (ld * ud) - 0) / 2 ^ 124 + (m * 2 ^ 30 * (D * D) - m * (ld + ud) * D) / 2 ^ 94 =
      -(m * (D * 2 ^ 30 - ld) * (ud - D * 2 ^ 30)) / 2 ^ 124 := by field_simp; ring
  rw [e, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (mul_nonneg hm (by linarith)) (by linarith)) (by positivity)

end McCormick

lemma step_kind7 {lp up d : ℕ} (hk : d % 8 = 7) (yn : Bool) (m : ℕ) (k : K) (data rp rn tp tn ap an : ℕ) :
    step P lp up d yn m k data rp rn tp tn ap an =
      sel yn (mcRow lp up d m k data rp rn tp tn ap an) (k data rp rn tp tn ap an) := by
  unfold step
  simp only []
  rw [beqk hk 4, beqk hk 7]
  rfl

lemma descOK_mc {d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 7) :
    keyOK sp (.mc (kf d 0) (kf d 1) (kf d 2)) = true ∧ f13 d 0 = sp.canon (kf d 0) (kf d 1) ∧
    f13 d 1 = kf d 0 ∧ f13 d 2 = kf d 1 ∧ f13 d 3 = kf d 2 ∧ dflag d = decide (kf d 0 = kf d 1) := by
  unfold descOK at hd
  simp only [] at hd
  rw [beqF hk 0 (by decide), sel_false, beqF hk 1 (by decide), sel_false, beqF hk 2 (by decide), sel_false,
    beqF hk 3 (by decide), sel_false, beqF hk 4 (by decide), sel_false, beqF hk 5 (by decide), sel_false,
    beqF hk 6 (by decide), sel_false] at hd
  simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6⟩

lemma mc_val_bound {m v : ℕ} (hv : v < 2 ^ 33) : m * v ≤ m * 2 ^ 36 :=
  Nat.mul_le_mul_left _ (by omega)

theorem stepOK_mc (hkp : KPFacts sp P) {lp up d : ℕ} (hd : descOK sp d = true) (hk : d % 8 = 7)
    (yn : Bool) (m : ℕ) : StepOK sp P lp up d yn m := by
  cases yn
  · exact noop_stepOK (fun k data rp rn tp tn ap an => by rw [step_kind7 hk]; rfl)
  obtain ⟨hkey, hf0, hf1, hf2, hf3, hflag⟩ := descOK_mc hd hk
  generalize kf d 0 = a at hkey hf0 hf1 hf2 hf3 hflag
  generalize kf d 1 = b at hkey hf0 hf1 hf2 hf3 hflag
  generalize kf d 2 = q at hkey hf0 hf1 hf2 hf3 hflag
  have hkey' := hkey
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq] at hkey'
  obtain ⟨⟨ha, hb⟩, hq⟩ := hkey'
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnb : sp.nB ≤ sp.oT := by rw [oT_eq]; omega
  have hz : sp.canon a b < sp.oT := canon_lt hkp.wf ha hb
  have g := get32_lt
  have hm30 : Nat.shiftLeft m 30 ≤ m * 2 ^ 36 := by rw [shl30]; exact Nat.mul_le_mul_left _ (by norm_num)
  have hstep0 : ∀ k data rp rn tp tn ap an, step P lp up d true m k data rp rn tp tn ap an =
      mcRow lp up d m k data rp rn tp tn ap an := fun k data rp rn tp tn ap an => by
    rw [step_kind7 hk, sel_true]
  -- the point facts
  have hx : ∀ p t, Pt sp lp up p t →
      xval sp p t (sp.canon a b) = mass sp p a * mass sp p b ∧ xval sp p t a = mass sp p a ∧
      xval sp p t b = mass sp p b ∧
      (get32 lp a : ℝ) / 2 ^ 30 ≤ mass sp p a ∧ mass sp p a ≤ (get32 up a : ℝ) / 2 ^ 30 ∧
      (get32 lp b : ℝ) / 2 ^ 30 ≤ mass sp p b ∧ mass sp p b ≤ (get32 up b : ℝ) / 2 ^ 30 :=
    fun p t hpt => ⟨xval_canon hkp.wf ha hb, xval_m ha, xval_m hb, (hpt.box a ha).1, (hpt.box a ha).2,
      (hpt.box b hb).1, (hpt.box b hb).2⟩
  by_cases hab : a = b
  · subst hab
    have hfl : dflag d = true := by rw [hflag]; simp
    interval_cases q
    · -- d = e, q = 0
      refine ⟨[(a, m * (2 * get32 lp a))], [(sp.canon a a, Nat.shiftLeft m 30)], 0, 0, 0,
        m * (get32 lp a * get32 lp a), ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_true, hf3, show Nat.beq 0 0 = true from rfl, sel_true, hf0, hf1, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨by omega, mc_val_bound (by have := g lp a; omega)⟩
        · exact ⟨hz, hm30⟩
      · intro p t hpt
        obtain ⟨hz', hd', -, hl, hu, -, -⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          Nat.cast_ofNat, sub_self, zero_div, zero_mul]
        have key := mcd0 (m := (m : ℝ)) (ld := (get32 lp a : ℝ)) (D := mass sp p a) hm
        ring_nf at key ⊢; linarith
    · -- d = e, q = 1
      refine ⟨[(a, m * (2 * get32 up a))], [(sp.canon a a, Nat.shiftLeft m 30)], 0, 0, 0,
        m * (get32 up a * get32 up a), ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_true, hf3, show Nat.beq 1 0 = false from rfl, sel_false,
          show Nat.beq 1 1 = true from rfl, sel_true, hf0, hf1, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨by omega, mc_val_bound (by have := g up a; omega)⟩
        · exact ⟨hz, hm30⟩
      · intro p t hpt
        obtain ⟨hz', hd', -, hl, hu, -, -⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          Nat.cast_ofNat, sub_self, zero_div, zero_mul]
        have key := mcd0 (m := (m : ℝ)) (ld := (get32 up a : ℝ)) (D := mass sp p a) hm
        ring_nf at key ⊢; linarith
    all_goals
      -- d = e, q ∈ {2, 3}
      refine ⟨[(sp.canon a a, Nat.shiftLeft m 30)], [(a, m * (get32 lp a + get32 up a))], 0, 0,
        m * (get32 lp a * get32 up a), 0, ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_true, hf3]
        first
          | rw [show Nat.beq 2 0 = false from rfl, sel_false, show Nat.beq 2 1 = false from rfl, sel_false]
          | rw [show Nat.beq 3 0 = false from rfl, sel_false, show Nat.beq 3 1 = false from rfl, sel_false]
        rw [hf0, hf1, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hz, hm30⟩
        · exact ⟨by omega, mc_val_bound (by have := g lp a; have := g up a; omega)⟩
      · intro p t hpt
        obtain ⟨hz', hd', -, hl, hu, -, -⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          Nat.cast_add, Nat.cast_ofNat, sub_self, zero_div, zero_mul]
        have key := mcd2 (m := (m : ℝ)) hm hl hu
        ring_nf at key ⊢; linarith
  · have hfl : dflag d = false := by rw [hflag]; simp [hab]
    interval_cases q
    · refine ⟨[(a, m * get32 lp b), (b, m * get32 lp a)], [(sp.canon a b, Nat.shiftLeft m 30)], 0, 0, 0,
        m * (get32 lp a * get32 lp b), ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_false, hf3, show Nat.beq 0 0 = true from rfl, sel_true, hf0, hf1, hf2, atc_eq, atc_eq,
          atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨by omega, mc_val_bound (by have := g lp b; omega)⟩
        · exact ⟨by omega, mc_val_bound (by have := g lp a; omega)⟩
        · exact ⟨hz, hm30⟩
      · intro p t hpt
        obtain ⟨hz', hd', he', hl, hu, hl', hu'⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', he', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          sub_self, zero_div, zero_mul]
        have key := mc0 (m := (m : ℝ)) hm hl hl'
        ring_nf at key ⊢; linarith
    · refine ⟨[(a, m * get32 up b), (b, m * get32 up a)], [(sp.canon a b, Nat.shiftLeft m 30)], 0, 0, 0,
        m * (get32 up a * get32 up b), ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_false, hf3, show Nat.beq 1 0 = false from rfl, sel_false,
          show Nat.beq 1 1 = true from rfl, sel_true, hf0, hf1, hf2, atc_eq, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨by omega, mc_val_bound (by have := g up b; omega)⟩
        · exact ⟨by omega, mc_val_bound (by have := g up a; omega)⟩
        · exact ⟨hz, hm30⟩
      · intro p t hpt
        obtain ⟨hz', hd', he', hl, hu, hl', hu'⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', he', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          sub_self, zero_div, zero_mul]
        have key := mc1 (m := (m : ℝ)) hm hu hu'
        ring_nf at key ⊢; linarith
    · refine ⟨[(sp.canon a b, Nat.shiftLeft m 30)], [(a, m * get32 up b), (b, m * get32 lp a)], 0, 0,
        m * (get32 lp a * get32 up b), 0, ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_false, hf3, show Nat.beq 2 0 = false from rfl, sel_false,
          show Nat.beq 2 1 = false from rfl, sel_false, show Nat.beq 2 2 = true from rfl, sel_true,
          hf0, hf1, hf2, atc_eq, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨hz, hm30⟩
        · exact ⟨by omega, mc_val_bound (by have := g up b; omega)⟩
        · exact ⟨by omega, mc_val_bound (by have := g lp a; omega)⟩
      · intro p t hpt
        obtain ⟨hz', hd', he', hl, hu, hl', hu'⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', he', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          sub_self, zero_div, zero_mul]
        have key := mc2 (m := (m : ℝ)) hm hl hu'
        ring_nf at key ⊢; linarith
    · refine ⟨[(sp.canon a b, Nat.shiftLeft m 30)], [(a, m * get32 lp b), (b, m * get32 up a)], 0, 0,
        m * (get32 up a * get32 lp b), 0, ?_, ?_, by simp, ?_⟩
      · intro k data rp rn tp tn ap an
        rw [hstep0]; unfold mcRow; simp only []
        rw [hfl, sel_false, hf3, show Nat.beq 3 0 = false from rfl, sel_false,
          show Nat.beq 3 1 = false from rfl, sel_false, show Nat.beq 3 2 = false from rfl, sel_false,
          hf0, hf1, hf2, atc_eq, atc_eq, atc_eq]
        simp [packL, raw_add, raw_mul]
      · intro e he
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨hz, hm30⟩
        · exact ⟨by omega, mc_val_bound (by have := g lp b; omega)⟩
        · exact ⟨by omega, mc_val_bound (by have := g up a; omega)⟩
      · intro p t hpt
        obtain ⟨hz', hd', he', hl, hu, hl', hu'⟩ := hx p t hpt
        unfold vq
        simp only [dotL_cons, dotL_nil, add_zero, hz', hd', he', cast_shl30, Nat.cast_mul, Nat.cast_zero,
          sub_self, zero_div, zero_mul]
        have key := mc3 (m := (m : ℝ)) hm hu hl'
        ring_nf at key ⊢; linarith

end AutocorrK
