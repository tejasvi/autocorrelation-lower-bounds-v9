import Autocorr.KSound.Step

/-!
# Soundness of the kernel leaf check

`leafOK P a b lp up cnt data = true` implies that every admissible point of the packed box has a window
with `q_W ≥ a/b`.
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

variable {sp : Spec} {P : KP}

theorem stepOK_all (hkp : KPFacts sp P) {lp up r : ℕ} (hr : r < P.NR) (yn : Bool) (m : ℕ) :
    StepOK sp P lp up (desc P r) yn m := by
  have hd := tableOK_desc hkp.table hr
  have h8 : desc P r % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rcases (show desc P r % 8 = 0 ∨ desc P r % 8 = 1 ∨ desc P r % 8 = 2 ∨ desc P r % 8 = 3 ∨
      desc P r % 8 = 4 ∨ desc P r % 8 = 5 ∨ desc P r % 8 = 6 ∨ desc P r % 8 = 7 by omega)
    with h | h | h | h | h | h | h | h
  · exact stepOK_win hkp hd h yn m
  · exact stepOK_P hkp hd h yn m
  · exact stepOK_G hkp hd h yn m
  · exact stepOK_tree hkp hd h yn m
  · exact stepOK_ZA hkp hd h yn m
  · exact stepOK_rlt hkp hd h yn m
  · exact stepOK_sym hkp h yn m
  · exact stepOK_mc hkp hd h yn m

lemma vq_append (p : ℕ → ℝ) (t : ℝ) (L1 N1 L2 N2 : List (ℕ × ℕ)) (a1 b1 c1 d1 a2 b2 c2 d2 : ℕ) :
    vq sp p t (L1 ++ L2) (N1 ++ N2) (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) =
      vq sp p t L1 N1 a1 b1 c1 d1 + vq sp p t L2 N2 a2 b2 c2 d2 := by
  unfold vq; rw [dotL_append, dotL_append]; push_cast; ring

/-- The CPS dual loop amounts to a fold. -/
theorem loop_spec (hkp : KPFacts sp P) (lp up : ℕ) (fin : K) :
    ∀ cnt data rp rn tp tn ap an, loop P lp up fin cnt data rp rn tp tn ap an = true →
    ∃ (data' : ℕ) (Lp Ln : List (ℕ × ℕ)) (dtp dtn dap dan : ℕ),
      fin data' (rp + packL Lp) (rn + packL Ln) (tp + dtp) (tn + dtn) (ap + dap) (an + dan) = true ∧
      (∀ e ∈ Lp ++ Ln, e.1 < sp.oT ∧ e.2 ≤ 2 ^ 108) ∧ Lp.length + Ln.length ≤ 70 * cnt ∧
      (∀ p t, Pt sp lp up p t → vq sp p t Lp Ln dtp dtn dap dan ≤ 0) := by
  intro cnt
  induction cnt with
  | zero =>
    intro data rp rn tp tn ap an h
    exact ⟨data, [], [], 0, 0, 0, 0, by simpa using (show fin data rp rn tp tn ap an = true from h),
      by simp, by simp, fun p t _ => by simp [vq]⟩
  | succ cnt ih =>
    intro data rp rn tp tn ap an h
    simp only [loop] at h
    -- the record
    set r := Nat.mod data 154742504910672534362390528 with hr
    set ri := Nat.mod r 16384 with hri
    by_cases hok : ri + 1 ≤ P.NR
    · rw [show Nat.ble (Nat.add ri 1) P.NR = true from Nat.ble_eq.mpr hok, sel_true] at h
      have hlt : ri < P.NR := by omega
      have hm : Nat.shiftRight r 15 < 2 ^ 72 := by
        have : r < 2 ^ 87 := by rw [hr, raw_mod]; exact Nat.mod_lt _ (by norm_num)
        rw [raw_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
        calc r < 2 ^ 87 := this
          _ = 2 ^ 72 * 2 ^ 15 := by norm_num
      obtain ⟨Lp1, Ln1, a1, b1, c1, d1, hstep, hb1, hl1, hv1⟩ :=
        stepOK_all hkp hlt (Nat.beq (Nat.mod (Nat.shiftRight r 14) 2) 1) (Nat.shiftRight r 15) (lp := lp) (up := up)
      rw [hstep] at h
      obtain ⟨data', Lp2, Ln2, a2, b2, c2, d2, hfin, hb2, hl2, hv2⟩ := ih _ _ _ _ _ _ _ h
      refine ⟨data', Lp1 ++ Lp2, Ln1 ++ Ln2, a1 + a2, b1 + b2, c1 + c2, d1 + d2, ?_, ?_, ?_, ?_⟩
      · rw [packL_append, packL_append]
        simpa only [add_assoc] using hfin
      · intro e he
        simp only [List.mem_append] at he
        rcases he with (he | he) | (he | he)
        · obtain ⟨h1, h2⟩ := hb1 e (List.mem_append_left _ he)
          exact ⟨h1, h2.trans (by
            calc Nat.shiftRight r 15 * 2 ^ 36 ≤ 2 ^ 72 * 2 ^ 36 := Nat.mul_le_mul_right _ hm.le
              _ = 2 ^ 108 := by norm_num)⟩
        · exact hb2 e (List.mem_append_left _ he)
        · obtain ⟨h1, h2⟩ := hb1 e (List.mem_append_right _ he)
          exact ⟨h1, h2.trans (by
            calc Nat.shiftRight r 15 * 2 ^ 36 ≤ 2 ^ 72 * 2 ^ 36 := Nat.mul_le_mul_right _ hm.le
              _ = 2 ^ 108 := by norm_num)⟩
        · exact hb2 e (List.mem_append_right _ he)
      · simp only [List.length_append]; nlinarith
      · intro p t hpt
        rw [vq_append]
        linarith [hv1 p t hpt, hv2 p t hpt]
    · rw [show Nat.ble (Nat.add ri 1) P.NR = false from ble_false hok, sel_false] at h
      exact absurd h (by simp)

/-! ## The m columns -/

lemma sum_accD_nat {L : List (ℕ × ℕ)} {S : ℕ} (hL : ∀ e ∈ L, e.1 < S) :
    ∑ c ∈ Finset.range S, accD L c = (L.map Prod.snd).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [List.map_cons, List.sum_cons, ← ih (fun f hf => hL f (List.mem_cons_of_mem _ hf))]
    simp only [accD_cons, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single e.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (hL e (List.mem_cons_self ..))) h

lemma sum_snd_le {L : List (ℕ × ℕ)} {B : ℕ} (hL : ∀ e ∈ L, e.2 ≤ B) : (L.map Prod.snd).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun f hf => hL f (List.mem_cons_of_mem _ hf))
    have := hL e (List.mem_cons_self ..)
    nlinarith

lemma mcols_succ (lp up k pv nv c ap an : ℕ) :
    mcols lp up (k + 1) pv nv c ap an =
      sel (Nat.ble (Nat.mod nv 87112285931760246646623899502532662132736)
          (Nat.mod pv 87112285931760246646623899502532662132736))
        (mcols lp up k (Nat.shiftRight pv 136) (Nat.shiftRight nv 136) (Nat.add c 1)
          (Nat.add ap (Nat.mul (Nat.sub (Nat.mod pv 87112285931760246646623899502532662132736)
            (Nat.mod nv 87112285931760246646623899502532662132736)) (get32 lp c))) an)
        (mcols lp up k (Nat.shiftRight pv 136) (Nat.shiftRight nv 136) (Nat.add c 1) ap
          (Nat.add an (Nat.mul (Nat.sub (Nat.mod nv 87112285931760246646623899502532662132736)
            (Nat.mod pv 87112285931760246646623899502532662132736)) (get32 up c)))) := rfl

lemma mcols_eq (lp up : ℕ) : ∀ (k : ℕ) (Pd Nd : ℕ → ℕ) (c ap an : ℕ),
    (∀ i < k, Pd i < 2 ^ 136) → (∀ i < k, Nd i < 2 ^ 136) →
    mcols lp up k (pk 136 Pd k) (pk 136 Nd k) c ap an =
      (ap + ∑ i ∈ Finset.range k, (if Nd i ≤ Pd i then (Pd i - Nd i) * get32 lp (c + i) else 0),
       an + ∑ i ∈ Finset.range k, (if Nd i ≤ Pd i then 0 else (Nd i - Pd i) * get32 up (c + i))) := by
  intro k
  induction k with
  | zero => intro Pd Nd c ap an _ _; simp [mcols]
  | succ k ih =>
    intro Pd Nd c ap an hP hN
    have hx : pk 136 Pd (k + 1) % 87112285931760246646623899502532662132736 = Pd 0 := by
      have := pk_digit (w := 136) (j := 0) hP (by omega)
      simpa using this
    have hy : pk 136 Nd (k + 1) % 87112285931760246646623899502532662132736 = Nd 0 := by
      have := pk_digit (w := 136) (j := 0) hN (by omega)
      simpa using this
    have hsP : pk 136 Pd (k + 1) >>> 136 = pk 136 (fun i => Pd (i + 1)) k := by
      rw [Nat.shiftRight_eq_div_pow, show (136 : ℕ) = 136 * 1 by norm_num, pk_div hP (by omega)]; simp
    have hsN : pk 136 Nd (k + 1) >>> 136 = pk 136 (fun i => Nd (i + 1)) k := by
      rw [Nat.shiftRight_eq_div_pow, show (136 : ℕ) = 136 * 1 by norm_num, pk_div hN (by omega)]; simp
    rw [mcols_succ]
    simp only [raw_mod, raw_shiftRight] at *
    rw [hx, hy, hsP, hsN]
    by_cases h : Nd 0 ≤ Pd 0
    · rw [ble_true h, sel_true]
      rw [ih _ _ _ _ _ (fun i hi => hP _ (by omega)) (fun i hi => hN _ (by omega))]
      simp only [Finset.sum_range_succ', if_pos h, raw_add, raw_mul, raw_sub, add_zero]
      congr 1
      · have : ∀ i ∈ Finset.range k, (if Nd (i + 1) ≤ Pd (i + 1) then (Pd (i + 1) - Nd (i + 1)) *
            get32 lp (c + 1 + i) else 0) = (if Nd (i + 1) ≤ Pd (i + 1) then (Pd (i + 1) - Nd (i + 1)) *
            get32 lp (c + (i + 1)) else 0) := fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega]
        rw [Finset.sum_congr rfl this]; ring
      · have : ∀ i ∈ Finset.range k, (if Nd (i + 1) ≤ Pd (i + 1) then 0 else (Nd (i + 1) - Pd (i + 1)) *
            get32 up (c + 1 + i)) = (if Nd (i + 1) ≤ Pd (i + 1) then 0 else (Nd (i + 1) - Pd (i + 1)) *
            get32 up (c + (i + 1))) := fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega]
        rw [Finset.sum_congr rfl this]
    · rw [ble_false h, sel_false]
      rw [ih _ _ _ _ _ (fun i hi => hP _ (by omega)) (fun i hi => hN _ (by omega))]
      simp only [Finset.sum_range_succ', if_neg h, raw_add, raw_mul, raw_sub, add_zero]
      congr 1
      · have : ∀ i ∈ Finset.range k, (if Nd (i + 1) ≤ Pd (i + 1) then (Pd (i + 1) - Nd (i + 1)) *
            get32 lp (c + 1 + i) else 0) = (if Nd (i + 1) ≤ Pd (i + 1) then (Pd (i + 1) - Nd (i + 1)) *
            get32 lp (c + (i + 1)) else 0) := fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega]
        rw [Finset.sum_congr rfl this]
      · have : ∀ i ∈ Finset.range k, (if Nd (i + 1) ≤ Pd (i + 1) then 0 else (Nd (i + 1) - Pd (i + 1)) *
            get32 up (c + 1 + i)) = (if Nd (i + 1) ≤ Pd (i + 1) then 0 else (Nd (i + 1) - Pd (i + 1)) *
            get32 up (c + (i + 1))) := fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega]
        rw [Finset.sum_congr rfl this]; ring

/-! ## The final comparison -/

lemma xval_01 {p : ℕ → ℝ} (hp : Adm sp p) (t : ℝ) {k : ℕ} (hk1 : sp.oZ ≤ k) (hk2 : k < sp.oT) :
    0 ≤ xval sp p t k ∧ xval sp p t k ≤ 1 := by
  have hp01 : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.nonneg i, p_le_one hp i⟩
  have hm01 : ∀ b, 0 ≤ mass sp p b ∧ mass sp p b ≤ 1 := fun b => ⟨mass_nonneg hp b, mass_le_one hp b⟩
  unfold xval
  rw [if_neg (by omega)]
  split_ifs
  · exact ⟨mul_nonneg (hp01 _).1 (hp01 _).1, mul_le_one₀ (hp01 _).2 (hp01 _).1 (hp01 _).2⟩
  · exact ⟨mul_nonneg (hm01 _).1 (hm01 _).1, mul_le_one₀ (hm01 _).2 (hm01 _).1 (hm01 _).2⟩
  · exact sum_mul_sum_le_one hp _
  · exact sum_mul_sum_le_one hp _

lemma final_ineq {n2 b a dap dan MP MN NEG TP dtp dtn S1 S2 t Cr : ℝ} (hn2 : 0 < n2) (hb : 0 < b)
    (F1 : b * (n2 * (dan + (MN + NEG * 2 ^ 30)) + TP) + a * n2 * 2 ^ 124 ≤ b * (n2 * (dap + MP)))
    (F2 : (dap - dan) / 2 ^ 124 + (S1 + S2) / 2 ^ 94 + (dtp - dtn) / (n2 * 2 ^ 64) * t ≤ 0)
    (F3 : MP - MN ≤ 2 ^ 30 * S1) (F4 : -NEG ≤ S2)
    (F5 : -TP ≤ 2 ^ 60 * ((Cr - dtn) * t)) (hC : Cr = n2 * 2 ^ 64 + dtp) :
    a ≤ t * b := by
  subst hC
  have F2' : n2 * (dap - dan) + n2 * 2 ^ 30 * (S1 + S2) + 2 ^ 60 * ((dtp - dtn) * t) ≤ 0 := by
    have h := mul_nonpos_of_nonneg_of_nonpos (show (0 : ℝ) ≤ n2 * 2 ^ 124 by positivity) F2
    have e : n2 * 2 ^ 124 * ((dap - dan) / 2 ^ 124 + (S1 + S2) / 2 ^ 94 + (dtp - dtn) / (n2 * 2 ^ 64) * t) =
        n2 * (dap - dan) + n2 * 2 ^ 30 * (S1 + S2) + 2 ^ 60 * ((dtp - dtn) * t) := by
      field_simp
    linarith
  have h3 := mul_le_mul_of_nonneg_left F3 hn2.le
  have h4 := mul_le_mul_of_nonneg_left F4 (show (0 : ℝ) ≤ n2 * 2 ^ 30 by positivity)
  have key : n2 * (dap - dan + MP - MN - 2 ^ 30 * NEG) - TP ≤ n2 * 2 ^ 124 * t := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left key hb.le
  have h6 : a * (n2 * 2 ^ 124) ≤ t * b * (n2 * 2 ^ 124) := by nlinarith
  exact le_of_mul_le_mul_right h6 (by positivity)

/-- The real-valued content of an accepted final comparison. -/
theorem fin_bound (hkp : KPFacts sp P) {lp up a b : ℕ} (hb : 0 < b) {Lp Ln : List (ℕ × ℕ)}
    {dtp dtn dap dan data : ℕ}
    (hfin : fin P lp up a b data (0 + packL Lp) (0 + packL Ln) (2 * P.n * 18446744073709551616 + dtp)
      (0 + dtn) (0 + dap) (0 + dan) = true)
    (hbd : ∀ e ∈ Lp ++ Ln, e.1 < sp.oT ∧ e.2 ≤ 2 ^ 108) (hlen : Lp.length + Ln.length ≤ 70 * 16383)
    {p : ℕ → ℝ} {t : ℝ} (hpt : Pt sp lp up p t) (hv : vq sp p t Lp Ln dtp dtn dap dan ≤ 0) :
    (a : ℝ) / b ≤ t := by
  set S := sp.oT with hS
  set nB := sp.nB with hnB
  have hnBS : nB ≤ S := by rw [hS, hnB, oT_eq]; omega
  set RP := accD Lp with hRP
  set RN := accD Ln with hRN
  have hcolP : ∀ e ∈ Lp, e.1 < S := fun e he => (hbd e (List.mem_append_left _ he)).1
  have hcolN : ∀ e ∈ Ln, e.1 < S := fun e he => (hbd e (List.mem_append_right _ he)).1
  have hRPb : ∀ c, RP c ≤ 70 * 16383 * 2 ^ 108 := fun c =>
    (accD_le (fun e he => (hbd e (List.mem_append_left _ he)).2) c).trans
      (Nat.mul_le_mul_right _ (by omega))
  have hRNb : ∀ c, RN c ≤ 70 * 16383 * 2 ^ 108 := fun c =>
    (accD_le (fun e he => (hbd e (List.mem_append_right _ he)).2) c).trans
      (Nat.mul_le_mul_right _ (by omega))
  have h70 : 70 * 16383 * 2 ^ 108 < 2 ^ 129 := by norm_num
  have h129 : (2 : ℕ) ^ 129 ≤ 2 ^ 135 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h135 : (2 : ℕ) ^ 135 ≤ 2 ^ 136 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hP135 : ∀ c, RP c < 2 ^ 135 := fun c => by have := hRPb c; omega
  have hN135 : ∀ c, RN c < 2 ^ 135 := fun c => by have := hRNb c; omega
  have hP136 : ∀ c < S, RP c < 2 ^ 136 := fun c _ => by have := hP135 c; omega
  have hN136 : ∀ c < S, RN c < 2 ^ 136 := fun c _ => by have := hN135 c; omega
  rw [zero_add, zero_add, zero_add, zero_add, zero_add] at hfin
  generalize hC : 2 * P.n * 18446744073709551616 + dtp = C at hfin
  rw [packL_eq_pk hcolP, packL_eq_pk hcolN] at hfin
  unfold fin at hfin
  simp only [raw_add, raw_sub, raw_mul, raw_mod, raw_pow, raw_shiftRight, raw_shiftLeft] at hfin
  rw [hkp.nB, hkp.NC1, hkp.n] at hfin
  rw [← hnB, ← hS, ← hRP, ← hRN] at hfin
  rw [pk_mod hP136 hnBS, pk_mod hN136 hnBS, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    pk_div hP136 hnBS, pk_div hN136 hnBS] at hfin
  rw [mcols_eq lp up nB RP RN 0 0 0 (fun c hc => hP136 c (by omega)) (fun c hc => hN136 c (by omega))]
    at hfin
  have hsum : ∑ c ∈ Finset.range (S - nB), (RN (c + nB) - RP (c + nB)) < W1 := by
    have hsplitN : ∑ c ∈ Finset.range S, RN c =
        ∑ c ∈ Finset.range nB, RN c + ∑ c ∈ Finset.range (S - nB), RN (c + nB) := by
      rw [← Finset.sum_range_add_sum_Ico _ hnBS, Finset.sum_Ico_eq_sum_range]
      congr 1; refine Finset.sum_congr rfl (fun c _ => by rw [add_comm])
    calc ∑ c ∈ Finset.range (S - nB), (RN (c + nB) - RP (c + nB))
        ≤ ∑ c ∈ Finset.range (S - nB), RN (c + nB) := Finset.sum_le_sum (fun c _ => Nat.sub_le _ _)
      _ ≤ ∑ c ∈ Finset.range S, RN c := by rw [hsplitN]; omega
      _ = (Ln.map Prod.snd).sum := sum_accD_nat hcolN
      _ ≤ Ln.length * 2 ^ 108 := sum_snd_le (fun e he => (hbd e (List.mem_append_right _ he)).2)
      _ ≤ (70 * 16383) * 2 ^ 108 := Nat.mul_le_mul_right _ (by omega)
      _ < W1 := by norm_num [W1]
  rw [swarNeg_eq _ _ _ (fun c _ => hP135 _) (fun c _ => hN135 _) hsum] at hfin
  simp only [zero_add, Nat.ble_eq] at hfin
  -- abbreviations (generalized, so that no big literal is ever unfolded)
  generalize hMP : (∑ i ∈ Finset.range nB, (if RN i ≤ RP i then (RP i - RN i) * get32 lp i else 0)) = MP at hfin
  generalize hMN : (∑ i ∈ Finset.range nB, (if RN i ≤ RP i then 0 else (RN i - RP i) * get32 up i)) = MN at hfin
  generalize hNEG : (∑ c ∈ Finset.range (S - nB), (RN (c + nB) - RP (c + nB))) = NEG at hfin
  rw [show (21267647932558653966460912964485513216 : ℕ) = 2 ^ 124 by norm_num, Nat.shiftLeft_eq] at hfin
  generalize hTP : sel (Nat.ble (C + 1) dtn) ((3 * (dtn - C)) <<< 60) 0 = TP at hfin
  have hn : (0 : ℝ) < 2 * sp.n := by have := sp.wf_n_pos hkp.wf; positivity
  set x := xval sp p t with hx
  -- (F2) the real inequality from vq ≤ 0
  have F2 : ((dap : ℝ) - dan) / 2 ^ 124 + (∑ c ∈ Finset.range nB, ((RP c : ℝ) - RN c) * x c +
      ∑ c ∈ Finset.Ico nB S, ((RP c : ℝ) - RN c) * x c) / 2 ^ 94 +
      ((dtp : ℝ) - dtn) / (2 * sp.n * 2 ^ 64) * t ≤ 0 := by
    have e1 := sum_accD hcolP x
    have e2 := sum_accD hcolN x
    unfold vq at hv
    rw [← e1, ← e2, ← Finset.sum_sub_distrib] at hv
    rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hnBS, ← Finset.range_eq_Ico]
    simpa only [sub_mul] using hv
  -- (F3) m columns
  have F3 : (MP : ℝ) - MN ≤ 2 ^ 30 * ∑ c ∈ Finset.range nB, ((RP c : ℝ) - RN c) * x c := by
    rw [← hMP, ← hMN]; push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    obtain ⟨hl, hu⟩ := hpt.box c hc
    have hxc : x c = mass sp p c := xval_m hc
    rw [hxc]
    split_ifs with h
    · rw [Nat.cast_sub h]
      have hnn : (0 : ℝ) ≤ (RP c : ℝ) - RN c := sub_nonneg.mpr (by exact_mod_cast h)
      rw [div_le_iff₀ (by positivity)] at hl
      nlinarith
    · rw [Nat.cast_sub (by omega)]
      have hnp : (RP c : ℝ) - RN c ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (by omega : RP c ≤ RN c))
      rw [le_div_iff₀ (by positivity)] at hu
      nlinarith
  -- (F4) [0,1] columns
  have F4 : -(NEG : ℝ) ≤ ∑ c ∈ Finset.Ico nB S, ((RP c : ℝ) - RN c) * x c := by
    rw [← hNEG, Finset.sum_Ico_eq_sum_range]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun c hc => ?_)
    rw [Finset.mem_range] at hc
    have hcb := xval_01 hpt.adm t (k := nB + c) (by rw [oZ_eq]; omega) (by omega)
    rw [add_comm c nB]
    rcases le_total (RN (nB + c)) (RP (nB + c)) with h | h
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have : (RN (nB + c) : ℝ) ≤ RP (nB + c) := by exact_mod_cast h
      nlinarith [hcb.1]
    · rw [Nat.cast_sub h]
      have : (RP (nB + c) : ℝ) ≤ RN (nB + c) := by exact_mod_cast h
      nlinarith [hcb.1, hcb.2]
  -- (F5) the t column
  have F5 : -(TP : ℝ) ≤ 2 ^ 60 * (((C : ℝ) - dtn) * t) := by
    rw [← hTP]
    by_cases h : C + 1 ≤ dtn
    · rw [ble_true h, sel_true, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
      have h' : (C : ℝ) - dtn ≤ 0 := sub_nonpos.mpr (by exact_mod_cast (by omega : C ≤ dtn))
      have h60 : ((2 ^ 60 : ℕ) : ℝ) = 2 ^ 60 := by norm_num
      rw [h60]
      have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
      rw [h3]
      nlinarith [hpt.t0, hpt.t3]
    · rw [ble_false h, sel_false]
      have h' : (dtn : ℝ) ≤ C := by exact_mod_cast (by omega : dtn ≤ C)
      simp only [Nat.cast_zero, neg_zero]
      have := hpt.t0
      positivity
  have hCr : (C : ℝ) = 2 * sp.n * 2 ^ 64 + dtp := by
    rw [← hC, hkp.n]; push_cast; norm_num
  -- (F1) the accepted comparison over ℝ
  have F1 : (b : ℝ) * (2 * sp.n * (dan + (MN + NEG * 2 ^ 30)) + TP) + a * (2 * sp.n) * 2 ^ 124 ≤
      b * (2 * sp.n * (dap + MP)) := by exact_mod_cast hfin
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  exact final_ineq hn hbR F1 F2 F3 F4 F5 hCr

/-- An accepted kernel leaf check covers its packed box. -/
theorem leafOK_sound (hkp : KPFacts sp P) {a b lp up cnt data : ℕ} (hb : 0 < b) (h3 : (a : ℝ) / b ≤ 3)
    (h : leafOK P a b lp up cnt data = true) : BoxOKK sp ((a : ℝ) / b) (lp, up) := by
  unfold leafOK at h
  by_cases hc : cnt ≤ 16383
  · rw [ble_true hc, sel_true] at h
    obtain ⟨data', Lp, Ln, dtp, dtn, dap, dan, hfin, hbd, hlen, hvq⟩ :=
      loop_spec hkp lp up (fin P lp up a b) cnt data 0 0 (Nat.mul (Nat.mul 2 P.n) 18446744073709551616)
        0 0 0 h
    intro p hp hbox
    by_contra hng
    have hn := sp.wf_n_pos hkp.wf
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
    have htlam : t < (a : ℝ) / b := by
      by_contra hge
      push Not at hge
      apply hng
      refine ⟨cm.1, cm.2, hcm'.1, hcm'.2, ?_⟩
      have hk := hpos cm hcm'.1
      rw [ht, hval] at hge
      simp only at hge
      rw [div_mul_eq_mul_div, le_div_iff₀ hk] at hge
      linarith
    have ht3 : t ≤ 3 := by linarith
    have hwin : ∀ c1 c2, c1 ≤ c2 → c2 + 2 ≤ 2 * sp.n →
        2 * (sp.n : ℝ) / ((c2 : ℝ) - c1 + 2) * wsum sp p c1 c2 ≤ t :=
      fun c1 c2 h12 h2 => hmax (c1, c2) (hmem c1 c2 h12 h2)
    have hpt : Pt sp lp up p t := ⟨hp, hbox, ht0, ht3, hwin⟩
    have := fin_bound hkp hb hfin hbd (by nlinarith) hpt (hvq p t hpt)
    linarith
  · rw [ble_false hc, sel_false] at h; exact absurd h (by simp)

end AutocorrK
