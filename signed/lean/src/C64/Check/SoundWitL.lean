import C64.Check.SoundWind

/-!
# Soundness of the checker, part 7: witness leaves (the representative measure `Σ m_k δ_{t_k}`)
-/

namespace C64Chk

open MeasureTheory Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### The atomic measure of a list of atoms -/

/-- `Σ m_k δ_{t_k}`. -/
noncomputable def atomicL (as : List (Q × Q)) : Measure ℝ :=
  (as.map fun a => ENNReal.ofReal a.2.val • Measure.dirac a.1.val).sum

theorem atomicL_cons (a : Q × Q) (as : List (Q × Q)) :
    atomicL (a :: as) = ENNReal.ofReal a.2.val • Measure.dirac a.1.val + atomicL as := by
  simp [atomicL]

theorem atomicL_univ : ∀ as : List (Q × Q), atomicL as Set.univ = (as.map fun a => ENNReal.ofReal a.2.val).sum
  | [] => by simp [atomicL]
  | a :: as => by
    rw [atomicL_cons, Measure.add_apply, Measure.smul_apply, atomicL_univ as]
    simp

theorem sum_ofReal_lt_top : ∀ as : List (Q × Q), (as.map fun a => ENNReal.ofReal a.2.val).sum < ⊤
  | [] => by simp
  | a :: as => by
    rw [List.map_cons, List.sum_cons]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, sum_ofReal_lt_top as⟩

instance (as : List (Q × Q)) : IsFiniteMeasure (atomicL as) := ⟨by rw [atomicL_univ]; exact sum_ofReal_lt_top as⟩

theorem atomicL_compl : ∀ as : List (Q × Q), (∀ a ∈ as, |a.1.val| ≤ 1 / 2) →
    atomicL as (Set.Icc (-1 / 2 : ℝ) (1 / 2))ᶜ = 0
  | [], _ => by simp [atomicL]
  | a :: as, h => by
    rw [atomicL_cons, Measure.add_apply, Measure.smul_apply, atomicL_compl as (fun b hb => h b (by simp [hb])),
      Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator_of_notMem]
    · simp
    · simp only [Set.mem_compl_iff, not_not, Set.mem_Icc]
      have := abs_le.1 (h a (by simp)); constructor <;> linarith [this.1, this.2]

theorem sum_ofReal_eq : ∀ as : List (Q × Q), (∀ a ∈ as, 0 ≤ a.2.val) →
    (as.map fun a => ENNReal.ofReal a.2.val).sum = ENNReal.ofReal (msum as)
  | [], _ => by simp [msum]
  | a :: as, h => by
    rw [List.map_cons, List.sum_cons, sum_ofReal_eq as (fun b hb => h b (by simp [hb]))]
    have h0 : 0 ≤ msum as := List.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact h y (by simp [hy]))
    rw [← ENNReal.ofReal_add (h a (by simp)) h0]
    simp [msum]

theorem integrable_atomicL (f : ℝ → ℂ) : ∀ as : List (Q × Q), Integrable f (atomicL as)
  | [] => by simp [atomicL]
  | a :: as => by
    rw [atomicL_cons]
    exact ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top).add_measure (integrable_atomicL f as)

theorem hat_atomicL {as : List (Q × Q)} (hA : AtomsOK as) (z : ℂ) : C64.hat (atomicL as) z = wsum as z := by
  induction as with
  | nil => simp [C64.hat, atomicL, wsum]
  | cons a as ih =>
    have ha := hA a (by simp)
    have ih' := ih (fun b hb => hA b (by simp [hb]))
    unfold C64.hat at ih' ⊢
    rw [atomicL_cons, integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
      (integrable_atomicL _ as), integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ha.2.2.2, ih']
    simp [wsum, Complex.real_smul]

theorem classA_atomicL {as : List (Q × Q)} (hA : AtomsOK as) {τ : ℝ} (hsum : msum as ≤ τ) :
    C64.ClassA τ (atomicL as) :=
  ⟨inferInstance, atomicL_compl as (fun a ha => (hA a ha).2.1),
    by rw [atomicL_univ, sum_ofReal_eq as (fun a ha => (hA a ha).2.2.2)]; exact ENNReal.ofReal_le_ofReal hsum⟩


/-! ### Witness leaves -/

theorem inBox_ok {w : CBall} {B : Box4} {Q' : C64.Box} {z : ℂ} (hz : memC P z w) (hB : Box4OK P Q' B)
    (h : inBox w B = true) : Q'.mem z := by
  unfold inBox at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hP := two_pow_pos' P
  have r1 := mem_iff_lo_hi.1 hz.1
  have r2 := mem_iff_lo_hi.1 hz.2
  have b1 := (mem_iff_lo_hi.1 hB.1).2
  have b2 := (mem_iff_lo_hi.1 hB.2.1).1
  have b3 := (mem_iff_lo_hi.1 hB.2.2.1).2
  have b4 := (mem_iff_lo_hi.1 hB.2.2.2).1
  have c1 : (B.1.hi : ℝ) / 2 ^ P ≤ (w.re.lo : ℝ) / 2 ^ P := div_le_div_of_nonneg_right (by exact_mod_cast h1) hP.le
  have c2 : (w.re.hi : ℝ) / 2 ^ P ≤ (B.2.1.lo : ℝ) / 2 ^ P := div_le_div_of_nonneg_right (by exact_mod_cast h2) hP.le
  have c3 : (B.2.2.1.hi : ℝ) / 2 ^ P ≤ (w.im.lo : ℝ) / 2 ^ P := div_le_div_of_nonneg_right (by exact_mod_cast h3) hP.le
  have c4 : (w.im.hi : ℝ) / 2 ^ P ≤ (B.2.2.2.lo : ℝ) / 2 ^ P := div_le_div_of_nonneg_right (by exact_mod_cast h4) hP.le
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem pinsIn_ok {g : Glob} {as : List (Q × Q)} (hA : AtomsOK as) :
    ∀ (ps : List ℂ) (pins : List (CBall × PtT × Q)) (bx : List (ℕ × ℕ × ℕ)),
    List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧ 0 < pb.2.2.d) ps pins →
    pinsIn g.cfg as pins (pinBoxes g.P pins bx) = true →
    ∀ x ∈ pqL ps pins bx, x.2.mem (wsum as x.1)
  | [], _, _, _, _ => by intro x hx; simp [pqL] at hx
  | p :: ps, pb :: pins, b :: bx, hF, h => by
    obtain ⟨hp, hrest⟩ := List.forall₂_cons.1 hF
    obtain ⟨d, i, k⟩ := b
    simp only [pinBoxes, pinsIn, Bool.and_eq_true, Option.any_eq_true] at h
    obtain ⟨⟨w, hw, hin⟩, h'⟩ := h
    have hwz := sumK_ok hp.1 as (fun a ha => ⟨(hA a ha).1, (hA a ha).2.2.1⟩) hw
    intro x hx
    simp only [pqL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact inBox_ok hwz (boxB_ok pb.2.2 hp.2.2 d i k) hin
    · exact pinsIn_ok hA ps pins bx hrest h' x hx
  | _ :: _, [], _, hF, _ => by simp at hF
  | p :: ps, pb :: pins, [], hF, h => by intro x hx; simp [pqL] at hx

theorem tileOf_ok {g : Glob} (hg : GlobOK g) {i : ℕ} {E : EllB} (h : tileOf g i = some E) :
    ∃ cT : ℂ, ∃ aT bT : ℝ, 0 < aT ∧ 0 < bT ∧ EllOK g.P cT aT bT E := by
  unfold tileOf at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem : t ∈ g.tiles := List.mem_of_getElem? ht
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg.tiles t hmem
  refine ⟨⟨t.1.val, t.2.1.val⟩, t.2.2.1.val, t.2.2.2.val, ?_, ?_, ⟨mem_Qball h1, mem_Qball h2, mem_Qball h3, mem_Qball h4⟩⟩
  · unfold Q.val; exact div_pos (by exact_mod_cast h5) (by exact_mod_cast h3)
  · unfold Q.val; exact div_pos (by exact_mod_cast h6) (by exact_mod_cast h4)

theorem checkWit_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {dat : ℕ} (h : checkWit g A bx dat = true) :
    C64.LeafSettledL g.tau.val zc ((A.r : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) := by
  unfold checkWit witOK at h
  set w := rdWit dat
  simp only [Option.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨E, hE, ⟨mn, md⟩, hmm, hex, r', hr', wz, hwz, hball⟩ := h
  obtain ⟨cT, aT, bT, haT, hbT, hEok⟩ := tileOf_ok hg hE
  obtain ⟨hAt, hmd, hms⟩ := atomsOK_ok w.as hmm
  unfold witExact at hex
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hex
  obtain ⟨⟨⟨⟨⟨htw, htwd⟩, hττ⟩, hmτ⟩, hsgd⟩, hsg⟩ := hex
  unfold witBall at hball
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hball
  obtain ⟨⟨⟨⟨hrr, hcross⟩, hpins⟩, htas⟩, hwo⟩ := hball
  have hP := two_pow_pos' g.P
  set tn := w.tw.n.toNat
  set td := w.tw.d
  have htn : 0 < tn := by simp only [tn]; omega
  have htn' : ((tn : ℕ) : ℝ) = (w.tw.n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg htw.le
  have htd' : (0 : ℝ) < td := by exact_mod_cast htwd
  have hmd' : (0 : ℝ) < md := by exact_mod_cast hmd
  -- τ ≤ τ' and Σ m ≤ τ'
  have hτ'eq : w.tw.val = (tn : ℝ) / td := by unfold Q.val; rw [htn']
  have hττ' : g.tau.val ≤ (tn : ℝ) / td := by
    rw [← hτ'eq]; unfold Q.val
    have h1 : (0 : ℝ) < g.tau.d := by have := lt_trans hg.tn hg.tlt; exact_mod_cast this
    rw [div_le_div_iff₀ h1 htd']; exact_mod_cast hττ
  have hmsτ : msum w.as ≤ (tn : ℝ) / td := by
    rw [hms, ← hτ'eq]; unfold Q.val
    rw [div_le_div_iff₀ hmd' htd']; exact_mod_cast hmτ
  -- the witness measure
  set ν := atomicL w.as
  have hνA : C64.ClassA ((tn : ℝ) / td) ν := classA_atomicL hAt hmsτ
  have hwzν := sumK_ok hA.hzc w.as (fun a ha => ⟨(hAt a ha).1, (hAt a ha).2.2.1⟩) hwz
  have hσ1 : 1 ≤ w.sg.val := by
    unfold Q.val
    have : (0 : ℝ) < w.sg.d := by exact_mod_cast hsgd
    rw [le_div_iff₀ this, one_mul]; exact_mod_cast hsg
  have hν : C64.PinnedL ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) ν := by
    refine ⟨hνA, ⟨w.sg.val, hσ1, ?_⟩, ?_⟩
    · rw [hat_atomicL hAt]
      have hm := C64Num.CBall.memC_sub hwzν (C64Num.CBall.memC_mulR (mem_Qball (P := g.P) hsgd) hA.hSc)
      refine (norm_le_normHi hm).trans ?_
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcross) hP.le
    · intro x hx
      rw [hat_atomicL hAt]
      exact pinsIn_ok hAt ps A.pins bx hA.hpins hpins x hx
  -- the tile and the winding number
  have htile := checkTAs_ok hg hA hbx hEok htn htwd w.N 0 w.dat htas
  have hmS : msum w.as ≤ (Ball.cdiv (mn.toNat * 2 ^ g.P) md : ℝ) / 2 ^ g.P := by
    have hmn : 0 ≤ mn := by
      have : (0 : ℝ) ≤ (mn : ℝ) / md := by
        rw [← hms]; exact List.sum_nonneg (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact (hAt y hy).2.2.2)
      have := (div_nonneg_iff.1 this)
      rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact_mod_cast h1
      · linarith
    have hc := cdiv_spec (mn.toNat * 2 ^ g.P) md hmd
    push_cast at hc
    have e : ((mn.toNat : ℕ) : ℝ) = (mn : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hmn
    rw [e] at hc
    rw [hms, le_div_iff₀ hP]
    calc (mn : ℝ) / md * 2 ^ g.P = (mn : ℝ) * 2 ^ g.P / md := by ring
      _ ≤ _ := hc
  obtain ⟨-, n, hn, hwind⟩ := windOdd_ok hg hEok hAt hmS hwo
  refine C64.leafSettledL_of_witness hττ' (div_le_div_of_nonneg_right (by exact_mod_cast hrr) hP.le) haT hbT
    (fun q hq μ ν' hμ hν' θ hθ => htile q ⟨by simpa using hq.1, hq.2⟩ μ ν' hμ hν' θ hθ) hν hn ?_
  have : (fun q => C64.G ν (C64.ellipse cT aT bT q)) =
      fun q => C64.S (C64.ellipse cT aT bT q) - wsum w.as (C64.ellipse cT aT bT q) := by
    funext q; unfold C64.G; rw [hat_atomicL hAt]
  rw [this]; exact hwind

end C64Chk
