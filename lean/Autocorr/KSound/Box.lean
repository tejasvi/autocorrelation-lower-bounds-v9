import Autocorr.KSound.Digits
import Autocorr.Cert.SoundMain
import AutocorrK.Table

/-!
# Packed boxes and the soundness of kernel propagation

A packed box `(lp, up)` holds `L_b = get32 lp b / 2^30`, `U_b = get32 up b / 2^30`.
-/

namespace AutocorrK

open Autocorr.Cert

variable {sp : Spec}

/-- `p` lies in the packed box. -/
def InBoxK (sp : Spec) (p : ℕ → ℝ) (lp up : ℕ) : Prop :=
  ∀ b < sp.nB, ((get32 lp b : ℕ) : ℝ) / 2 ^ 30 ≤ mass sp p b ∧ mass sp p b ≤ ((get32 up b : ℕ) : ℝ) / 2 ^ 30

/-- Every admissible point of the packed box is good. -/
def BoxOKK (sp : Spec) (lam : ℝ) (bx : ℕ × ℕ) : Prop :=
  ∀ p, Adm sp p → InBoxK sp p bx.1 bx.2 → Good sp lam p

lemma nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax sel
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq.mpr h'] at h
    show a = max a b
    exact (max_eq_left (by omega)).symm
  · show b = max a b
    exact (max_eq_right (Nat.ble_eq.mp h)).symm

lemma nmin_eq (a b : ℕ) : nmin a b = min a b := by
  unfold nmin sel
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq.mpr h'] at h
    show b = min a b
    exact (min_eq_right (by omega)).symm
  · show a = min a b
    exact (min_eq_left (Nat.ble_eq.mp h)).symm

section

variable {p : ℕ → ℝ}

lemma low_le (hp : Adm sp p) {lp up : ℕ} (h : InBoxK sp p lp up) {b : ℕ} (hb : b < sp.nB) :
    get32 lp b ≤ 2 ^ 30 := by
  have h1 := (h b hb).1
  have h2 := mass_le_one hp b
  have : ((get32 lp b : ℕ) : ℝ) ≤ 2 ^ 30 := by
    have := h1.trans h2
    rw [div_le_one (by positivity)] at this
    exact this
  exact_mod_cast this

/-- Writing a valid lower bound into slot `i`. -/
lemma inbox_setL {lp up : ℕ} (h : InBoxK sp p lp up) {i v : ℕ} (hv : v < 2 ^ 32)
    (hvalid : i < sp.nB → (v : ℝ) / 2 ^ 30 ≤ mass sp p i) : InBoxK sp p (set32 lp i v) up := by
  intro b hb
  rw [get32_set32 _ _ _ _ hv]
  split_ifs with hbi
  · subst hbi; exact ⟨hvalid hb, (h b hb).2⟩
  · exact h b hb

lemma inbox_setU {lp up : ℕ} (h : InBoxK sp p lp up) {i v : ℕ} (hv : v < 2 ^ 32)
    (hvalid : i < sp.nB → mass sp p i ≤ (v : ℝ) / 2 ^ 30) : InBoxK sp p lp (set32 up i v) := by
  intro b hb
  rw [get32_set32 _ _ _ _ hv]
  split_ifs with hbi
  · subst hbi; exact ⟨(h b hb).1, hvalid hb⟩
  · exact h b hb

lemma upd_eq (b c1 c2 lp up : ℕ) (k : ℕ → ℕ → ℕ × ℕ) :
    upd b c1 c2 lp up k = k
      (set32 (set32 (set32 lp b (nmax (get32 lp b) (get32 lp c1 + get32 lp c2))) c1
        (nmax (get32 lp c1) (get32 lp b - get32 up c2))) c2 (nmax (get32 lp c2) (get32 lp b - get32 up c1)))
      (set32 (set32 (set32 up b (nmin (get32 up b) (get32 up c1 + get32 up c2))) c1
        (nmin (get32 up c1) (get32 up b - get32 lp c2))) c2 (nmin (get32 up c2) (get32 up b - get32 lp c1))) :=
  rfl

/-- One propagation update at an internal block is sound. -/
theorem upd_sound (hw : sp.wf = true) (hp : Adm sp p) {b : ℕ} (hint : sp.isInt b = true)
    {lp up : ℕ} (h : InBoxK sp p lp up) :
    InBoxK sp p
      (set32 (set32 (set32 lp b (nmax (get32 lp b) (get32 lp (sp.blk b).c1 + get32 lp (sp.blk b).c2)))
        (sp.blk b).c1 (nmax (get32 lp (sp.blk b).c1) (get32 lp b - get32 up (sp.blk b).c2)))
        (sp.blk b).c2 (nmax (get32 lp (sp.blk b).c2) (get32 lp b - get32 up (sp.blk b).c1)))
      (set32 (set32 (set32 up b (nmin (get32 up b) (get32 up (sp.blk b).c1 + get32 up (sp.blk b).c2)))
        (sp.blk b).c1 (nmin (get32 up (sp.blk b).c1) (get32 up b - get32 lp (sp.blk b).c2)))
        (sp.blk b).c2 (nmin (get32 up (sp.blk b).c2) (get32 up b - get32 lp (sp.blk b).c1))) := by
  have hb := isInt_lt hint
  obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int hw hb hint
  have hm := mass_split hw p hint
  set c1 := (sp.blk b).c1
  set c2 := (sp.blk b).c2
  have hL1 := low_le hp h hc1
  have hL2 := low_le hp h hc2
  have hLb := low_le hp h hb
  have g := get32_lt
  obtain ⟨lb, ub⟩ := h b hb
  obtain ⟨l1, u1⟩ := h c1 hc1
  obtain ⟨l2, u2⟩ := h c2 hc2
  have m1 := mass_nonneg hp c1
  have m2 := mass_nonneg hp c2
  -- casts of truncated differences
  have sub_le : ∀ a c : ℕ, ((a - c : ℕ) : ℝ) ≤ max ((a : ℝ) - c) 0 := fun a c => by
    rcases le_total c a with hca | hca
    · rw [Nat.cast_sub hca]; exact le_max_left _ _
    · rw [Nat.sub_eq_zero_of_le hca]; simp
  refine inbox_setU (inbox_setU (inbox_setU ?_ ?_ ?_) ?_ ?_) ?_ ?_
  · -- lower bounds
    refine inbox_setL (inbox_setL (inbox_setL h ?_ ?_) ?_ ?_) ?_ ?_
    · rw [nmax_eq]; exact max_lt (g _ _) (by omega)
    · intro _; rw [nmax_eq, Nat.cast_max, ← max_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), max_le_iff]
      refine ⟨lb, ?_⟩; push_cast; rw [add_div, hm]; linarith
    · rw [nmax_eq]; exact max_lt (g _ _) (lt_of_le_of_lt (Nat.sub_le _ _) (g _ _))
    · intro _; rw [nmax_eq, Nat.cast_max, ← max_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), max_le_iff]
      refine ⟨l1, ?_⟩
      have := sub_le (get32 lp b) (get32 up c2)
      rw [div_le_iff₀ (by positivity)] at lb l1 ⊢
      rw [le_div_iff₀ (by positivity)] at u2
      calc ((get32 lp b - get32 up c2 : ℕ) : ℝ) ≤ max ((get32 lp b : ℝ) - get32 up c2) 0 := this
        _ ≤ mass sp p c1 * 2 ^ 30 := by
          apply max_le
          · rw [show mass sp p c1 = mass sp p b - mass sp p c2 by linarith]; nlinarith
          · positivity
    · rw [nmax_eq]; exact max_lt (g _ _) (lt_of_le_of_lt (Nat.sub_le _ _) (g _ _))
    · intro _; rw [nmax_eq, Nat.cast_max, ← max_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), max_le_iff]
      refine ⟨l2, ?_⟩
      have := sub_le (get32 lp b) (get32 up c1)
      rw [div_le_iff₀ (by positivity)] at lb l2 ⊢
      rw [le_div_iff₀ (by positivity)] at u1
      calc ((get32 lp b - get32 up c1 : ℕ) : ℝ) ≤ max ((get32 lp b : ℝ) - get32 up c1) 0 := this
        _ ≤ mass sp p c2 * 2 ^ 30 := by
          apply max_le
          · rw [show mass sp p c2 = mass sp p b - mass sp p c1 by linarith]; nlinarith
          · positivity
  -- upper bounds
  · rw [nmin_eq]; exact lt_of_le_of_lt (min_le_left _ _) (g _ _)
  · intro _; rw [nmin_eq, Nat.cast_min, ← min_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), le_min_iff]
    refine ⟨ub, ?_⟩; push_cast; rw [add_div, hm]; linarith
  · rw [nmin_eq]; exact lt_of_le_of_lt (min_le_left _ _) (g _ _)
  · intro _; rw [nmin_eq, Nat.cast_min, ← min_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), le_min_iff]
    refine ⟨u1, ?_⟩
    have hle : get32 lp c2 ≤ get32 up b := by
      have : ((get32 lp c2 : ℕ) : ℝ) ≤ get32 up b := by
        rw [div_le_iff₀ (by positivity)] at l2
        rw [le_div_iff₀ (by positivity)] at ub
        nlinarith
      exact_mod_cast this
    rw [Nat.cast_sub hle, sub_div]; linarith
  · rw [nmin_eq]; exact lt_of_le_of_lt (min_le_left _ _) (g _ _)
  · intro _; rw [nmin_eq, Nat.cast_min, ← min_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), le_min_iff]
    refine ⟨u2, ?_⟩
    have hle : get32 lp c1 ≤ get32 up b := by
      have : ((get32 lp c1 : ℕ) : ℝ) ≤ get32 up b := by
        rw [div_le_iff₀ (by positivity)] at l1
        rw [le_div_iff₀ (by positivity)] at ub
        nlinarith
      exact_mod_cast this
    rw [Nat.cast_sub hle, sub_div]; linarith

/-- `sweep` with an explicit count and table. -/
noncomputable def sweepN (P : KP) (m : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ lp up => (lp, up))
    (fun _ ih tab lp up =>
      let e := Nat.mod tab 2097152
      upd (Nat.mod e 128) (Nat.mod (Nat.shiftRight e 7) 128) (Nat.shiftRight e 14) lp up
        (ih (Nat.shiftRight tab 21)))
    m

noncomputable def intOKN (sp : Spec) (m : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih tab =>
      let e := Nat.mod tab 2097152
      let b := Nat.mod e 128
      Nat.blt b sp.nB && sp.isInt b && Nat.beq (Nat.mod (Nat.shiftRight e 7) 128) (sp.blk b).c1 &&
        Nat.beq (Nat.shiftRight e 14) (sp.blk b).c2 && ih (Nat.shiftRight tab 21))
    m

lemma sweep_eq' (P : KP) (lp up : ℕ) : sweep P lp up = sweepN P P.nInt P.intTab lp up := rfl
lemma intOK_eq' (sp : Spec) (P : KP) : intOK sp P = intOKN sp P.nInt P.intTab := rfl

theorem sweepN_sound (hw : sp.wf = true) (hp : Adm sp p) (P : KP) :
    ∀ (m tab lp up : ℕ), intOKN sp m tab = true → InBoxK sp p lp up →
      InBoxK sp p (sweepN P m tab lp up).1 (sweepN P m tab lp up).2 := by
  intro m
  induction m with
  | zero => intro tab lp up _ h; exact h
  | succ m ih =>
    intro tab lp up hok h
    simp only [intOKN, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hok
    obtain ⟨⟨⟨⟨hb, hint⟩, hc1⟩, hc2⟩, hrest⟩ := hok
    simp only [sweepN]
    rw [upd_eq]
    simp only [raw_mod, raw_shiftRight] at hc1 hc2 ⊢
    rw [hc1, hc2]
    exact ih _ _ _ hrest (upd_sound hw hp hint h)

theorem sweep_sound (hw : sp.wf = true) (hp : Adm sp p) {P : KP} (hP : intOK sp P = true)
    {lp up : ℕ} (h : InBoxK sp p lp up) : InBoxK sp p (sweep P lp up).1 (sweep P lp up).2 := by
  rw [sweep_eq']
  exact sweepN_sound hw hp P _ _ _ _ (by rw [← intOK_eq']; exact hP) h

theorem propK_sound (hw : sp.wf = true) (hp : Adm sp p) {P : KP} (hP : intOK sp P = true)
    (k : ℕ) {lp up : ℕ} (h : InBoxK sp p lp up) : InBoxK sp p (propK P k lp up).1 (propK P k lp up).2 := by
  induction k with
  | zero =>
    show InBoxK sp p (set32 lp 0 (nmax (get32 lp 0) 1073741824)) (set32 up 0 (nmin (get32 up 0) 1073741824))
    have hroot := mass_root hw hp
    have hn0 := sp.wf_nB_pos hw
    refine inbox_setU (inbox_setL h ?_ ?_) ?_ ?_
    · rw [nmax_eq]; exact max_lt (get32_lt _ _) (by norm_num)
    · intro _
      rw [nmax_eq, Nat.cast_max, ← max_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), max_le_iff,
        hroot]
      exact ⟨by rw [← hroot]; exact (h 0 hn0).1, by norm_num⟩
    · rw [nmin_eq]; exact lt_of_le_of_lt (min_le_left _ _) (get32_lt _ _)
    · intro _
      rw [nmin_eq, Nat.cast_min, ← min_div_div_right (show (0:ℝ) ≤ 2 ^ 30 by positivity), le_min_iff,
        hroot]
      exact ⟨by rw [← hroot]; exact (h 0 hn0).2, by norm_num⟩
  | succ k ih =>
    show InBoxK sp p (sweep P (propK P k lp up).1 (propK P k lp up).2).1
      (sweep P (propK P k lp up).1 (propK P k lp up).2).2
    exact sweep_sound hw hp hP ih

/-- The two children of a split cover the box. -/
theorem child_coverK (hw : sp.wf = true) (hp : Adm sp p) {P : KP} (hP : intOK sp P = true)
    {lp up b s : ℕ} (k0 k1 : ℕ) (hs : s < 2 ^ 32) (h : InBoxK sp p lp up) :
    InBoxK sp p (propK P k0 lp (set32 up b s)).1 (propK P k0 lp (set32 up b s)).2 ∨
    InBoxK sp p (propK P k1 (set32 lp b s) up).1 (propK P k1 (set32 lp b s) up).2 := by
  by_cases hm : mass sp p b ≤ (s : ℝ) / 2 ^ 30
  · left; exact propK_sound hw hp hP k0 (inbox_setU h hs (fun _ => hm))
  · right; exact propK_sound hw hp hP k1 (inbox_setL h hs (fun _ => (lt_of_not_ge hm).le))

end

end AutocorrK
