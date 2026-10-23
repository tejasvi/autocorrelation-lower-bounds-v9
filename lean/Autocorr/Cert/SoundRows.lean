import Autocorr.Cert.SoundBasic

/-!
# Soundness, part 2: the true point, column bounds and validity of every row

For an admissible `p` and `t ≥ 0` the "true point" `xval p t` assigns to every column index its
intended value: block masses, products `p_i p_j`, `m_d m_e`, band sums `P_c`, cumulative sums `G_c`
and `t`.  Every row produced by `rowOf` from a valid key holds at the true point.
-/

open scoped BigOperators

namespace Autocorr.Cert

variable {sp : Spec}

/-- `P_c = Σ_{i+j=c} p_i p_j` over ordered pairs `i, j < n`. -/
noncomputable def Pc (sp : Spec) (p : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, if i + j = c then p i * p j else 0

/-- `G_c = Σ_{i+j≤c} p_i p_j`. -/
noncomputable def Gc (sp : Spec) (p : ℕ → ℝ) (c : ℕ) : ℝ :=
  ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, if i + j ≤ c then p i * p j else 0

/-- Window sum `Σ_{c1 ≤ i+j ≤ c2} p_i p_j`. -/
noncomputable def wsum (sp : Spec) (p : ℕ → ℝ) (c1 c2 : ℕ) : ℝ :=
  ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n,
    if c1 ≤ i + j ∧ i + j ≤ c2 then p i * p j else 0

/-- The true point. -/
noncomputable def xval (sp : Spec) (p : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℝ :=
  if k < sp.oZ then mass sp p k
  else if k < sp.oZA then p ((k - sp.oZ) / sp.n) * p ((k - sp.oZ) % sp.n)
  else if k < sp.oP then mass sp p ((k - sp.oZA) / sp.nB) * mass sp p ((k - sp.oZA) % sp.nB)
  else if k < sp.oG then Pc sp p (k - sp.oP)
  else if k < sp.oT then Gc sp p (k - sp.oG)
  else t

/-- Value of a list of row entries at a point. -/
noncomputable def rowVal (ent : List (ℕ × ℚ)) (x : ℕ → ℝ) : ℝ :=
  (ent.map (fun e => ((e.2 : ℚ) : ℝ) * x e.1)).sum

/-- `lo ≤ v ≤ up` for the finite sides. -/
def RowValid (row : Row) (v : ℝ) : Prop :=
  (∀ l, row.lo = some l → ((l : ℚ) : ℝ) ≤ v) ∧ (∀ u, row.up = some u → v ≤ ((u : ℚ) : ℝ))

/-! ## Index arithmetic -/

lemma idx2_lt {a b n : ℕ} (ha : a < n) (hb : b < n) : a * n + b < n * n := by
  have : (a + 1) * n ≤ n * n := Nat.mul_le_mul_right n ha
  rw [Nat.add_mul, one_mul] at this
  omega

lemma idx2_div {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < n), Nat.div_eq_of_lt hb, zero_add]

lemma idx2_mod {a b n : ℕ} (hb : b < n) : (a * n + b) % n = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma oZ_eq : sp.oZ = sp.nB := rfl
lemma oZA_eq : sp.oZA = sp.nB + sp.n * sp.n := rfl
lemma oP_eq : sp.oP = sp.nB + sp.n * sp.n + sp.nB * sp.nB := rfl
lemma oG_eq : sp.oG = sp.nB + sp.n * sp.n + sp.nB * sp.nB + (2 * sp.n - 1) := rfl
lemma oT_eq : sp.oT = sp.nB + sp.n * sp.n + sp.nB * sp.nB + (2 * sp.n - 1) + (2 * sp.n - 1) := rfl
lemma NC_eq : sp.NC = sp.oT + 1 := rfl

variable {p : ℕ → ℝ} {t : ℝ}

lemma xval_m {b : ℕ} (hb : b < sp.nB) : xval sp p t b = mass sp p b := by
  unfold xval; rw [if_pos (by rw [oZ_eq]; exact hb)]

lemma xval_z {i j : ℕ} (hi : i < sp.n) (hj : j < sp.n) : xval sp p t (sp.zIdx i j) = p i * p j := by
  have hmin : min i j < sp.n := lt_of_le_of_lt (min_le_left _ _) hi
  have hmax : max i j < sp.n := max_lt hi hj
  have hlt := idx2_lt hmin hmax
  unfold xval Spec.zIdx
  rw [if_neg (by rw [oZ_eq]; omega), if_pos (by rw [oZA_eq, oZ_eq]; omega)]
  rw [show sp.oZ + min i j * sp.n + max i j - sp.oZ = min i j * sp.n + max i j by omega,
    idx2_div hmax, idx2_mod hmax]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

lemma xval_za {d e : ℕ} (hd : d < sp.nB) (he : e < sp.nB) :
    xval sp p t (sp.zaIdx d e) = mass sp p d * mass sp p e := by
  have hmin : min d e < sp.nB := lt_of_le_of_lt (min_le_left _ _) hd
  have hmax : max d e < sp.nB := max_lt hd he
  have hlt := idx2_lt hmin hmax
  unfold xval Spec.zaIdx
  rw [if_neg (by rw [oZ_eq, oZA_eq]; omega), if_neg (by rw [oZA_eq]; omega),
    if_pos (by rw [oP_eq, oZA_eq]; omega)]
  rw [show sp.oZA + min d e * sp.nB + max d e - sp.oZA = min d e * sp.nB + max d e by omega,
    idx2_div hmax, idx2_mod hmax]
  rcases le_total d e with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, mul_comm]

lemma xval_canon (h : sp.wf = true) {d e : ℕ} (hd : d < sp.nB) (he : e < sp.nB) :
    xval sp p t (sp.canon d e) = mass sp p d * mass sp p e := by
  unfold Spec.canon
  split_ifs with hl
  · rw [Bool.and_eq_true] at hl
    have hdl := (sp.wf_blk h hd)
    have hel := (sp.wf_blk h he)
    rw [xval_z (by omega) (by omega), mass_of_isLeaf p hl.1, mass_of_isLeaf p hl.2]
  · exact xval_za hd he

lemma xval_P {c : ℕ} (hc : c + 2 ≤ 2 * sp.n) : xval sp p t (sp.oP + c) = Pc sp p c := by
  unfold xval
  rw [if_neg (by rw [oZ_eq, oP_eq]; omega), if_neg (by rw [oZA_eq, oP_eq]; omega),
    if_neg (by omega), if_pos (by rw [oG_eq, oP_eq]; omega)]
  congr 1; omega

lemma xval_G {c : ℕ} (hc : c + 2 ≤ 2 * sp.n) : xval sp p t (sp.oG + c) = Gc sp p c := by
  unfold xval
  rw [if_neg (by rw [oZ_eq, oG_eq]; omega), if_neg (by rw [oZA_eq, oG_eq]; omega),
    if_neg (by rw [oP_eq, oG_eq]; omega), if_neg (by omega),
    if_pos (by rw [oT_eq, oG_eq]; omega)]
  congr 1; omega

lemma xval_T : xval sp p t sp.oT = t := by
  unfold xval
  rw [if_neg (by rw [oZ_eq, oT_eq]; omega), if_neg (by rw [oZA_eq, oT_eq]; omega),
    if_neg (by rw [oP_eq, oT_eq]; omega), if_neg (by rw [oG_eq, oT_eq]; omega), if_neg (lt_irrefl _)]

/-! ## Column bounds -/

lemma sum_mul_sum_le_one (hp : Adm sp p) (P : ℕ → ℕ → Prop) [∀ i j, Decidable (P i j)] :
    0 ≤ ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, (if P i j then p i * p j else 0) ∧
    ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, (if P i j then p i * p j else 0) ≤ 1 := by
  constructor
  · refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
    split_ifs
    · exact mul_nonneg (hp.nonneg i) (hp.nonneg j)
    · exact le_refl 0
  · calc ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, (if P i j then p i * p j else 0)
        ≤ ∑ i ∈ Finset.range sp.n, ∑ j ∈ Finset.range sp.n, p i * p j := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          split_ifs
          · exact le_refl _
          · exact mul_nonneg (hp.nonneg i) (hp.nonneg j)
      _ = (∑ i ∈ Finset.range sp.n, p i) * (∑ j ∈ Finset.range sp.n, p j) :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ = 1 := by rw [hp.sum1, one_mul]

lemma col_bounds (hp : Adm sp p) {bx : Box} (hbx : InBox sp p bx) (ht0 : 0 ≤ t) (ht3 : t ≤ 3)
    (k : ℕ) : ((lbOf sp bx k : ℚ) : ℝ) ≤ xval sp p t k ∧ xval sp p t k ≤ ((ubOf sp bx k : ℚ) : ℝ) := by
  have o1 : sp.oZ ≤ sp.oZA := by rw [oZ_eq, oZA_eq]; omega
  have o2 : sp.oZA ≤ sp.oP := by rw [oZA_eq, oP_eq]; omega
  have o3 : sp.oP ≤ sp.oG := by rw [oP_eq, oG_eq]; omega
  have o4 : sp.oG ≤ sp.oT := by rw [oG_eq, oT_eq]; omega
  unfold lbOf ubOf xval
  by_cases h0 : k < sp.oZ
  · simp only [if_pos h0]
    exact ⟨hbx.1 k (by rw [← oZ_eq]; exact h0), hbx.2 k (by rw [← oZ_eq]; exact h0)⟩
  simp only [if_neg h0]
  by_cases hT : k < sp.oT
  · simp only [if_pos hT, Rat.cast_zero, Rat.cast_one]
    have hp01 : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.nonneg i, p_le_one hp i⟩
    have hm01 : ∀ b, 0 ≤ mass sp p b ∧ mass sp p b ≤ 1 := fun b => ⟨mass_nonneg hp b, mass_le_one hp b⟩
    split_ifs
    · exact ⟨mul_nonneg (hp01 _).1 (hp01 _).1,
        mul_le_one₀ (hp01 _).2 (hp01 _).1 (hp01 _).2⟩
    · exact ⟨mul_nonneg (hm01 _).1 (hm01 _).1,
        mul_le_one₀ (hm01 _).2 (hm01 _).1 (hm01 _).2⟩
    · exact sum_mul_sum_le_one hp _
    · exact sum_mul_sum_le_one hp _
  · simp only [if_neg hT]
    have h1 : ¬ k < sp.oZA := by omega
    have h2 : ¬ k < sp.oP := by omega
    have h3 : ¬ k < sp.oG := by omega
    simp only [if_neg h1, if_neg h2, if_neg h3, Rat.cast_zero]
    exact ⟨ht0, by norm_num; exact ht3⟩

/-! ## Row values -/

@[simp] lemma rowVal_nil (x : ℕ → ℝ) : rowVal [] x = 0 := rfl

@[simp] lemma rowVal_cons (k : ℕ) (a : ℚ) (rest : List (ℕ × ℚ)) (x : ℕ → ℝ) :
    rowVal ((k, a) :: rest) x = (a : ℝ) * x k + rowVal rest x := by
  simp [rowVal]

lemma rowVal_append (l1 l2 : List (ℕ × ℚ)) (x : ℕ → ℝ) :
    rowVal (l1 ++ l2) x = rowVal l1 x + rowVal l2 x := by
  simp [rowVal, List.map_append, List.sum_append]

lemma rowVal_map_range (m : ℕ) (f : ℕ → ℕ × ℚ) (x : ℕ → ℝ) :
    rowVal ((List.range m).map f) x = ∑ i ∈ Finset.range m, (((f i).2 : ℚ) : ℝ) * x (f i).1 := by
  induction m with
  | zero => simp [rowVal]
  | succ m ih =>
    rw [List.range_succ, List.map_append, rowVal_append, ih, Finset.sum_range_succ]
    simp [rowVal]

lemma rowVal_filterMap_range (m : ℕ) (g : ℕ → Option (ℕ × ℚ)) (x : ℕ → ℝ) :
    rowVal ((List.range m).filterMap g) x =
      ∑ i ∈ Finset.range m, (match g i with | some e => ((e.2 : ℚ) : ℝ) * x e.1 | none => 0) := by
  induction m with
  | zero => simp [rowVal]
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append, rowVal_append, ih, Finset.sum_range_succ]
    congr 1
    cases hg : g m <;> simp [List.filterMap, hg, rowVal]

/-! ## Band-sum identities -/

lemma Pc_eq (c : ℕ) : Pc sp p c = ∑ i ∈ Finset.range sp.n,
    (if i ≤ c ∧ c - i < sp.n then p i * p (c - i) else 0) := by
  unfold Pc
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hic : i ≤ c
  · have : ∀ j, (i + j = c ↔ j = c - i) := fun j => by omega
    simp_rw [this]
    rw [Finset.sum_ite_eq' (Finset.range sp.n) (c - i) (fun j => p i * p j)]
    simp [hic, Finset.mem_range]
  · rw [Finset.sum_eq_zero (fun j _ => by rw [if_neg (by omega)])]
    rw [if_neg (by omega)]

lemma Gc_succ (c : ℕ) : Gc sp p (c + 1) = Pc sp p (c + 1) + Gc sp p c := by
  unfold Gc Pc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : i + j = c + 1
  · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
  · by_cases h2 : i + j ≤ c
    · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add]
    · rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]

lemma Gc_zero : Gc sp p 0 = Pc sp p 0 := by
  unfold Gc Pc
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : i + j = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

lemma wsum_eq_Gc_zero (c2 : ℕ) : wsum sp p 0 c2 = Gc sp p c2 := by
  unfold wsum Gc
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : i + j ≤ c2
  · rw [if_pos ⟨Nat.zero_le _, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

lemma wsum_eq_Gc_sub {c1 c2 : ℕ} (h1 : 0 < c1) (h12 : c1 ≤ c2) :
    wsum sp p c1 c2 = Gc sp p c2 - Gc sp p (c1 - 1) := by
  unfold wsum Gc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases ha : c1 ≤ i + j ∧ i + j ≤ c2
  · rw [if_pos ha, if_pos ha.2, if_neg (by omega), sub_zero]
  · by_cases hb : i + j ≤ c1 - 1
    · rw [if_neg ha, if_pos (by omega), if_pos hb, sub_self]
    · rw [if_neg ha, if_neg (by omega), if_neg hb, sub_self]

/-! ## Validity of each row -/

lemma valid_eq0 {row : Row} (hlo : row.lo = some 0) (hup : row.up = some 0) {v : ℝ} (hv : v = 0) :
    RowValid row v := by
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · rw [hlo, Option.some.injEq] at hl; subst hl; rw [hv]; simp
  · rw [hup, Option.some.injEq] at hu; subst hu; rw [hv]; simp

section Rows

variable {bx : Box}

lemma valid_win {c1 c2 : ℕ} (h12 : c1 ≤ c2) (h2 : c2 + 2 ≤ 2 * sp.n)
    (hwin : 2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t) :
    RowValid (rowOf sp bx (.win c1 c2)) (rowVal (rowOf sp bx (.win c1 c2)).ent (xval sp p t)) := by
  refine ⟨fun l hl => by simp [rowOf] at hl, fun u hu => ?_⟩
  simp only [rowOf, Option.some.injEq] at hu
  subst hu
  simp only [rowOf]
  rw [rowVal_cons, rowVal_cons, xval_G h2, xval_T]
  split_ifs with hc1
  · rw [rowVal_cons, rowVal_nil, xval_G (by omega)]
    rw [wsum_eq_Gc_sub hc1 h12] at hwin
    push_cast
    have e : 2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * (Gc sp p c2 - Gc sp p (c1 - 1)) =
        2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * Gc sp p c2 +
          -(2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2)) * Gc sp p (c1 - 1) := by ring
    linarith
  · have : c1 = 0 := by omega
    subst this
    rw [rowVal_nil]
    rw [wsum_eq_Gc_zero] at hwin
    push_cast at hwin ⊢
    linarith

lemma valid_P (hw : sp.wf = true) (hp : Adm sp p) {c : ℕ} (hc : c + 2 ≤ 2 * sp.n) :
    RowValid (rowOf sp bx (.P c)) (rowVal (rowOf sp bx (.P c)).ent (xval sp p t)) := by
  have key : rowVal (rowOf sp bx (.P c)).ent (xval sp p t) = 0 := by
    simp only [rowOf]
    rw [rowVal_cons, xval_P hc, rowVal_filterMap_range, Pc_eq, Rat.cast_one, one_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    split_ifs with h
    · simp only
      rw [xval_z hi h.2]
      push_cast; ring
    · simp
  exact valid_eq0 rfl rfl key

lemma valid_G {c : ℕ} (hc : c + 2 ≤ 2 * sp.n) :
    RowValid (rowOf sp bx (.G c)) (rowVal (rowOf sp bx (.G c)).ent (xval sp p t)) := by
  have key : rowVal (rowOf sp bx (.G c)).ent (xval sp p t) = 0 := by
    simp only [rowOf]
    rw [rowVal_cons, rowVal_cons, xval_G hc, xval_P hc]
    split_ifs with hc0
    · rw [rowVal_cons, rowVal_nil, xval_G (by omega)]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [Gc_succ, show c' + 1 - 1 = c' by omega]
      push_cast; ring
    · have : c = 0 := by omega
      subst this
      rw [rowVal_nil, Gc_zero]
      push_cast; ring
  exact valid_eq0 rfl rfl key

lemma valid_tree (hw : sp.wf = true) {b : ℕ} (hk : keyOK sp (.tree b) = true) :
    RowValid (rowOf sp bx (.tree b)) (rowVal (rowOf sp bx (.tree b)).ent (xval sp p t)) := by
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨hb, hint⟩ := hk
  obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int hw hb hint
  have key : rowVal (rowOf sp bx (.tree b)).ent (xval sp p t) = 0 := by
    simp only [rowOf]
    rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_m hb, xval_m hc1, xval_m hc2,
      mass_split hw p hint]
    push_cast; ring
  exact valid_eq0 rfl rfl key

lemma valid_ZA (hw : sp.wf = true) {d e s : ℕ} (hk : keyOK sp (.ZA d e s) = true) :
    RowValid (rowOf sp bx (.ZA d e s)) (rowVal (rowOf sp bx (.ZA d e s)).ent (xval sp p t)) := by
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨hd, he⟩, hs⟩, hsde⟩, hint⟩ := hk
  obtain ⟨hc1, hc2, -, -, -⟩ := sp.wf_int hw hs hint
  have hm := mass_split hw p hint
  have key : rowVal (rowOf sp bx (.ZA d e s)).ent (xval sp p t) = 0 := by
    simp only [rowOf]
    rw [rowVal_cons, xval_canon hw hd he]
    split_ifs with hde hsd
    · subst hde
      have : s = d := by rcases hsde with h | h <;> exact h
      subst this
      rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hc1 hc1,
        xval_canon hw hc1 hc2, xval_canon hw hc2 hc2, hm]
      push_cast; ring
    · subst hsd
      rw [rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hc1 he, xval_canon hw hc2 he, hm]
      push_cast; ring
    · have hse : s = e := by rcases hsde with h | h; exact absurd h hsd; exact h
      subst hse
      rw [rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hc1 hd, xval_canon hw hc2 hd, hm]
      push_cast; ring
  exact valid_eq0 rfl rfl key

lemma valid_rlt (hw : sp.wf = true) (hp : Adm sp p) {i : ℕ} (hk : keyOK sp (.rlt i) = true) :
    RowValid (rowOf sp bx (.rlt i)) (rowVal (rowOf sp bx (.rlt i)).ent (xval sp p t)) := by
  simp only [keyOK, decide_eq_true_eq] at hk
  obtain ⟨hl, -, -⟩ := sp.wf_leaf hw hk
  have key : rowVal (rowOf sp bx (.rlt i)).ent (xval sp p t) = 0 := by
    simp only [rowOf]
    rw [rowVal_append, rowVal_map_range, rowVal_cons, rowVal_nil, xval_m hl, mass_leaf hw p hk]
    have : ∑ j ∈ Finset.range sp.n, (((1 : ℚ) : ℝ)) * xval sp p t (sp.zIdx i j) =
        ∑ j ∈ Finset.range sp.n, p i * p j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [xval_z hk hj, Rat.cast_one, one_mul]
    simp only at this ⊢
    rw [this, ← Finset.mul_sum, hp.sum1]
    push_cast; ring
  exact valid_eq0 rfl rfl key

lemma valid_sym (hw : sp.wf = true) (hp : Adm sp p) :
    RowValid (rowOf sp bx .sym) (rowVal (rowOf sp bx .sym).ent (xval sp p t)) := by
  refine ⟨fun l hl => by simp [rowOf] at hl, fun u hu => ?_⟩
  simp only [rowOf, Option.some.injEq] at hu
  subst hu
  simp only [rowOf]
  rw [rowVal_map_range]
  have : ∑ i ∈ Finset.range sp.n,
      (((2 * (i : ℚ) - ((sp.n : ℚ) - 1) : ℚ)) : ℝ) * xval sp p t (sp.leaf i) =
      ∑ i ∈ Finset.range sp.n, (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * p i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [xval_m (sp.wf_leaf hw hi).1, mass_leaf hw p hi]
    push_cast; ring
  simp only at this ⊢
  rw [this]
  push_cast
  exact hp.half

lemma valid_mc (hw : sp.wf = true) (hbx : InBox sp p bx) {d e q : ℕ} (hk : keyOK sp (.mc d e q) = true) :
    RowValid (rowOf sp bx (.mc d e q)) (rowVal (rowOf sp bx (.mc d e q)).ent (xval sp p t)) := by
  simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨hd, he⟩, hq⟩ := hk
  have Ld := hbx.1 d hd
  have Ud := hbx.2 d hd
  have Le := hbx.1 e he
  have Ue := hbx.2 e he
  set md := mass sp p d
  set me := mass sp p e
  set ld : ℝ := ((bx.L.getD d 0 : ℚ) : ℝ)
  set ud : ℝ := ((bx.U.getD d 0 : ℚ) : ℝ)
  set le : ℝ := ((bx.L.getD e 0 : ℚ) : ℝ)
  set ue : ℝ := ((bx.U.getD e 0 : ℚ) : ℝ)
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · simp only [rowOf] at hl
    split_ifs at hl <;> exact absurd hl (by simp)
  · simp only [rowOf] at hu ⊢
    split_ifs at hu ⊢ with hde hq0 hq1 hq0' hq1' hq2'
    · simp only [Option.some.injEq] at hu; subst hu
      subst hde
      rw [rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd hd, xval_m hd]
      push_cast
      nlinarith [sq_nonneg (md - ld)]
    · simp only [Option.some.injEq] at hu; subst hu
      subst hde
      rw [rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd hd, xval_m hd]
      push_cast
      nlinarith [sq_nonneg (md - ud)]
    · simp only [Option.some.injEq] at hu; subst hu
      subst hde
      rw [rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd hd, xval_m hd]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr Ld) (sub_nonneg.mpr Ud)]
    · simp only [Option.some.injEq] at hu; subst hu
      rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd he, xval_m hd, xval_m he]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr Ld) (sub_nonneg.mpr Le)]
    · simp only [Option.some.injEq] at hu; subst hu
      rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd he, xval_m hd, xval_m he]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr Ud) (sub_nonneg.mpr Ue)]
    · simp only [Option.some.injEq] at hu; subst hu
      rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd he, xval_m hd, xval_m he]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr Ld) (sub_nonneg.mpr Ue)]
    · simp only [Option.some.injEq] at hu; subst hu
      rw [rowVal_cons, rowVal_cons, rowVal_cons, rowVal_nil, xval_canon hw hd he, xval_m hd, xval_m he]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr Ud) (sub_nonneg.mpr Le)]

end Rows

/-- Every row built from a valid key holds at the true point (for any `t` dominating all windows). -/
theorem row_valid (hw : sp.wf = true) (hp : Adm sp p) {bx : Box} (hbx : InBox sp p bx)
    (hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
      2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t)
    (key : RowKey) (hk : keyOK sp key = true) :
    RowValid (rowOf sp bx key) (rowVal (rowOf sp bx key).ent (xval sp p t)) := by
  cases key with
  | win c1 c2 =>
    simp only [keyOK, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact valid_win hk.1 hk.2 (hwin c1 c2 hk.1 hk.2)
  | P c =>
    simp only [keyOK, decide_eq_true_eq] at hk
    exact valid_P hw hp hk
  | G c =>
    simp only [keyOK, decide_eq_true_eq] at hk
    exact valid_G hk
  | tree b => exact valid_tree hw hk
  | ZA d e s => exact valid_ZA hw hk
  | rlt i => exact valid_rlt hw hp hk
  | sym => exact valid_sym hw hp
  | mc d e q => exact valid_mc hw hbx hk

end Autocorr.Cert
