import C64.Check.SoundLeaf

/-!
# Soundness of the checker, part 5: tile arcs (Lemma 6.4(b) along a tile)
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-- The tile condition at the parameter `q` of the tile `(c_T, a_T, b_T)`: no convex combination of two measures
of the pinned set vanishes at `z_T(q)`. -/
def TileCond (τ' : ℝ) (zc : ℂ) (r' : ℝ) (pq : List (ℂ × C64.Box)) (cT : ℂ) (aT bT : ℝ) (q : ℝ) : Prop :=
  ∀ μ ν : MeasureTheory.Measure ℝ, C64.PinnedL τ' zc r' pq μ → C64.PinnedL τ' zc r' pq ν →
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, C64.S (C64.ellipse cT aT bT q) -
      ((1 - θ) * C64.hat μ (C64.ellipse cT aT bT q) + θ * C64.hat ν (C64.ellipse cT aT bT q)) ≠ 0

theorem checkTAPiece_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ} {aT bT : ℝ}
    (hE : EllOK g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) {u v : ℤ × ℤ} {ys : List (ℤ × ℤ)}
    (hys : ys.length = ps.length) (hX : ((starRingEnd ℂ) (cOf v) * C64.S zc).re ≤ 0) {n0 n1 e : ℕ}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ g.P)
    (h : checkTAPiece g A E r' tn td (intC g.P u) (intC g.P v) (yTerms g.P true A.pins ys)
      (sumBox true (pinBoxes g.P A.pins bx) ys) n0 n1 e = true) :
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      TileCond ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) cT aT bT q := by
  unfold checkTAPiece at h
  simp only [Option.any_eq_true] at h
  obtain ⟨pd, hpd, T, hT, h⟩ := h
  unfold taPieceOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ha, htb⟩ := h
  have hP := two_pow_pos' g.P
  obtain ⟨hpdok, hrad⟩ := pieceD_ok hE h01 he hpd
  have hTok := ptT_ok hpdok.z hg.D1 hg.hD hT
  have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
  set ds := dsOf g.P ps A.pins bx ys
  have hpq : C64.pqOf ds = pqL ps A.pins bx := pqOf_dsOf ps A.pins bx ys hlen hbx hys
  have hbox := dsOf_bounds (P := g.P) (ps := ps) (pins_d hA.hpins) bx ys
  obtain ⟨-, hhi⟩ := sum_lo_dsOf (P := g.P) ps A.pins bx ys hlen hbx
  have hu := memC_intC (P := g.P) u
  have hv := memC_intC (P := g.P) v
  obtain ⟨-, hXhi⟩ := reConj_bounds hv hA.hSc
  have hrv : ‖cOf v‖ * ((r' : ℝ) / 2 ^ g.P) ≤ (mulU g.P (normHi (intC g.P v)) r' : ℝ) / 2 ^ g.P :=
    mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi hv) le_rfl
  obtain ⟨hF, hL⟩ := yTerms_ok hA.hpins true ys
  set pm := C64.ellipse cT aT bT (((n0 : ℝ) + n1) / 2 ^ (e + 1))
  have htb' := tbound_ok (czs := ((starRingEnd ℂ) (cOf u), pm) :: (-(starRingEnd ℂ) (cOf v), zc) ::
      yczs true ps ys) htb
    (List.Forall₂.cons (termOf_ok hTok (C64Num.CBall.memC_conj hu))
      (List.Forall₂.cons (termOf_ok hA.hzT (C64Num.CBall.memC_neg (C64Num.CBall.memC_conj hv))) hF))
    (by
      intro T' hT'
      simp only [List.mem_cons] at hT'
      rcases hT' with rfl | rfl | hT'
      · exact hTok.len
      · exact hA.hzT.len
      · exact hL T' hT')
  intro q hq μ ν hμ hν θ hθ
  rw [← hpq] at hμ hν
  obtain ⟨hS, hK⟩ := disc_bounds hu hpdok (hrad q hq)
  have hRHS : (aTA g A r' (intC g.P u) (intC g.P v) (sumBox true (pinBoxes g.P A.pins bx) ys) pd : ℝ) / 2 ^ g.P ≤
      ((starRingEnd ℂ) (cOf u) * C64.S (C64.ellipse cT aT bT q)).re - ((starRingEnd ℂ) (cOf v) * C64.S zc).re -
        ‖cOf v‖ * ((r' : ℝ) / 2 ^ g.P) - (ds.map fun d => d.hi).sum := by
    rw [hhi]
    unfold aTA
    push_cast
    rw [sub_div, sub_div, sub_div]
    linarith
  refine C64.pinnedL_tile_ne (by positivity) hbox hX (fun t ht => ?_)
    (lt_of_lt_of_le (div_pos (by exact_mod_cast ha) hP) hRHS) hμ hν hθ
  have h2 := htb' t ht
  have hfs : fsum (((starRingEnd ℂ) (cOf u), pm) :: (-(starRingEnd ℂ) (cOf v), zc) :: yczs true ps ys) t =
      ((starRingEnd ℂ) (cOf u) * C64.Kt t pm).re - C64.LamL (cOf v) zc ds t := by
    rw [show fsum (((starRingEnd ℂ) (cOf u), pm) :: (-(starRingEnd ℂ) (cOf v), zc) :: yczs true ps ys) t =
      ((starRingEnd ℂ) (cOf u) * C64.Kt t pm).re + (-(starRingEnd ℂ) (cOf v) * C64.Kt t zc).re +
        fsum (yczs true ps ys) t by simp only [fsum, List.map_cons, List.sum_cons]; ring]
    rw [(fsum_yczs (P := g.P) ps A.pins bx ys hlen hbx t).2]
    unfold C64.LamL
    simp only [neg_mul, Complex.neg_re]
    ring
  rw [hfs] at h2
  have hx : ((starRingEnd ℂ) (cOf u) * C64.Kt t (C64.ellipse cT aT bT q)).re - C64.LamL (cOf v) zc ds t ≤
      (((starRingEnd ℂ) (cOf u) * C64.Kt t pm).re - C64.LamL (cOf v) zc ds t) +
        (dPof g.P (intC g.P u) pd : ℝ) / 2 ^ g.P := by
    have := hK t ht; linarith
  exact lt_of_lt_of_le (tgt_bound htn htd ha hx h2) hRHS

theorem checkTA_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ} {aT bT : ℝ}
    (hE : EllOK g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) {u v : ℤ × ℤ} {ys : List (ℤ × ℤ)}
    (hys : ys.length = ps.length) (hX : ((starRingEnd ℂ) (cOf v) * C64.S zc).re ≤ 0) :
    ∀ (fuel n0 n1 e : ℕ), n0 ≤ n1 → e + fuel + 1 ≤ g.P →
    checkTA g A E r' tn td (intC g.P u) (intC g.P v) (yTerms g.P true A.pins ys)
      (sumBox true (pinBoxes g.P A.pins bx) ys) fuel n0 n1 e = true →
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      TileCond ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) cT aT bT q
  | 0, n0, n1, e, h01, he, h => checkTAPiece_ok hg hA hbx hE htn htd hys hX h01 (by omega) h
  | fuel + 1, n0, n1, e, h01, he, h => by
    unfold checkTA at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact checkTAPiece_ok hg hA hbx hE htn htd hys hX h01 (by omega) h
    · intro s hs
      have hm : ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) = ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; ring
      rcases le_total s (((n0 : ℝ) + n1) / 2 ^ (e + 1)) with hsm | hsm
      · refine checkTA_ok hg hA hbx hE htn htd hys hX fuel (2 * n0) (n0 + n1) (e + 1) (by omega) (by omega) h1 s
          ⟨?_, ?_⟩
        · push_cast; rw [pow_succ]
          have := hs.1; rw [show (2 * (n0 : ℝ)) / (2 ^ e * 2) = (n0 : ℝ) / 2 ^ e by field_simp]; exact this
        · rw [hm]; exact hsm
      · refine checkTA_ok hg hA hbx hE htn htd hys hX fuel (n0 + n1) (2 * n1) (e + 1) (by omega) (by omega) h2 s
          ⟨?_, ?_⟩
        · rw [hm]; exact hsm
        · push_cast; rw [pow_succ]
          have := hs.2; rw [show (2 * (n1 : ℝ)) / (2 ^ e * 2) = (n1 : ℝ) / 2 ^ e by field_simp]; exact this

theorem checkTAs_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {E : EllB} {cT : ℂ} {aT bT : ℝ}
    (hE : EllOK g.P cT aT bT E) {r' tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) :
    ∀ (N q0 s : ℕ), checkTAs g A E r' tn td (pinBoxes g.P A.pins bx) N q0 s = true →
    ∀ q ∈ Set.Icc ((q0 : ℝ) / 2 ^ g.EQ) 1,
      TileCond ((tn : ℝ) / td) zc ((r' : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) cT aT bT q
  | 0, _, _, h => by simp [checkTAs] at h
  | N + 1, q0, s, h => by
    unfold checkTAs at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hta, hrest⟩ := h
    set r := rdTA A.pins.length s
    unfold taOK at hta
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hta
    obtain ⟨⟨⟨h01, h1Q⟩, hXv⟩, hck⟩ := hta
    have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
    have hys : r.2.2.2.1.length = ps.length := by
      simp only [r, rdTA]; rw [rdPairs_length, hlen]
    have hP := two_pow_pos' g.P
    have hX : ((starRingEnd ℂ) (cOf r.2.2.1) * C64.S zc).re ≤ 0 := by
      rcases hXv with hXv | hXv
      · exact le_trans (reConj_bounds (memC_intC (P := g.P) r.2.2.1) hA.hSc).2
          (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hXv) hP.le)
      · have : cOf r.2.2.1 = 0 := by rw [hXv]; apply Complex.ext <;> simp [cOf]
        rw [this]; simp
    have hpiece := checkTA_ok hg hA hbx hE htn htd hys hX g.dT q0 r.1 g.EQ h01.le
      (by have := hg.hT; omega) hck
    have hEQ := two_pow_pos' g.EQ
    intro q hq
    rcases le_total q ((r.1 : ℝ) / 2 ^ g.EQ) with hq1 | hq1
    · exact hpiece q ⟨hq.1, hq1⟩
    · rcases hrest with heq | hrest
      · have : (r.1 : ℝ) / 2 ^ g.EQ = 1 := by
          rw [heq]; push_cast; exact div_self hEQ.ne'
        exact hpiece q ⟨hq.1, by rw [this]; exact hq.2⟩
      · exact checkTAs_ok hg hA hbx hE htn htd N r.1 r.2.2.2.2 hrest q ⟨hq1, hq.2⟩

end C64Chk
