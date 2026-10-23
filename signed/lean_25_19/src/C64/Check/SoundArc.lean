import C64.Check.SoundT

/-!
# Soundness of the checker, part 3: global facts, discs around arc points, type E arcs
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Global facts -/

/-- The facts of `checkGlob` that the arc proofs use. -/
structure GlobOK (g : Glob) : Prop where
  tn : 0 < g.tau.n
  tlt : (g.tau.n : ℤ) < g.tau.d
  cd : 0 < g.c.d
  ad : 0 < g.a.d
  bd : 0 < g.b.d
  an : 0 < g.a.n
  bn : 0 < g.b.n
  D1 : 1 ≤ g.D
  hE : g.ES + g.dE + 1 ≤ g.P
  hT : g.EQ + g.dT + 1 ≤ g.P
  hW : g.dW + 2 ≤ g.P
  hD : g.D + 1 ≤ g.P
  tiles : ∀ e ∈ g.tiles, 0 < e.1.d ∧ 0 < e.2.1.d ∧ 0 < e.2.2.1.d ∧ 0 < e.2.2.2.d ∧ 0 < e.2.2.1.n ∧
    0 < e.2.2.2.n

theorem checkGlob_ok {g : Glob} (h : checkGlob g = true) :
    GlobOK g ∧ windOdd g (T1B g) [] 0 = true := by
  unfold checkGlob globParams at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun e he => by
    have := h13 e he; tauto⟩, h14⟩

theorem tau_pos {g : Glob} (hg : GlobOK g) : 0 < g.tau.val := by
  unfold Q.val
  have h1 : (0 : ℝ) < g.tau.n := by exact_mod_cast hg.tn
  have h2 : (0 : ℝ) < g.tau.d := by
    have : (0 : ℤ) < g.tau.d := lt_trans hg.tn hg.tlt
    exact_mod_cast this
  positivity

theorem tau_lt_one {g : Glob} (hg : GlobOK g) : g.tau.val < 1 := by
  unfold Q.val
  have h2 : (0 : ℝ) < g.tau.d := by
    have : (0 : ℤ) < g.tau.d := lt_trans hg.tn hg.tlt
    exact_mod_cast this
  rw [div_lt_one h2]; exact_mod_cast hg.tlt

theorem tau_eq {g : Glob} (hg : GlobOK g) : g.tau.val = (g.tau.n.toNat : ℝ) / g.tau.d := by
  unfold Q.val; congr 1; exact_mod_cast (Int.toNat_of_nonneg hg.tn.le).symm

theorem T1_ok {g : Glob} (hg : GlobOK g) : EllOK g.P (g.c.val : ℂ) g.a.val g.b.val (T1B g) := by
  refine ⟨?_, ?_, mem_Qball hg.ad, mem_Qball hg.bd⟩
  · rw [Complex.ofReal_re]; exact mem_Qball hg.cd
  · rw [Complex.ofReal_im]
    have := mem_Qball (P := g.P) (q := ⟨0, 1⟩) (by norm_num)
    have e : Q.val ⟨0, 1⟩ = 0 := by simp [Q.val]
    rw [e] at this; exact this

/-! ### Discs around arc points -/

theorem re_conj_S_ge {u z zm : ℂ} {ρ L : ℝ} (hz : ‖z - zm‖ ≤ ρ)
    (hL : ∀ ζ ∈ Metric.closedBall zm ρ, ‖C64.S1 ζ‖ ≤ L) :
    ((starRingEnd ℂ) u * C64.S zm).re - ‖u‖ * (L * ρ) ≤ ((starRingEnd ℂ) u * C64.S z).re := by
  have hzU : z ∈ Metric.closedBall zm ρ := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
  have hcU : zm ∈ Metric.closedBall zm ρ := Metric.mem_closedBall_self ((norm_nonneg _).trans hz)
  have h1 := C64.norm_sub_S_le (convex_closedBall zm ρ) hL hzU hcU
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL zm hcU)
  have h2 : |((starRingEnd ℂ) u * (C64.S z - C64.S zm)).re| ≤ ‖u‖ * (L * ρ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hz hL0)) (norm_nonneg _)
  rw [mul_sub, Complex.sub_re] at h2
  linarith [(abs_le.1 h2).1]

theorem re_conj_Kt_le {u z zm : ℂ} {ρ Y t : ℝ} (ht : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) (hz : ‖z - zm‖ ≤ ρ)
    (hY : ∀ ζ ∈ Metric.closedBall zm ρ, |ζ.im| ≤ Y) :
    ((starRingEnd ℂ) u * C64.Kt t z).re ≤ ((starRingEnd ℂ) u * C64.Kt t zm).re + ‖u‖ * (π * Real.exp (π * Y) * ρ) := by
  have hzU : z ∈ Metric.closedBall zm ρ := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
  have hcU : zm ∈ Metric.closedBall zm ρ := Metric.mem_closedBall_self ((norm_nonneg _).trans hz)
  have ht' : t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := ht
  have h1 := C64.norm_sub_Kt_le ht' (convex_closedBall zm ρ) hY hzU hcU
  have h2 : |((starRingEnd ℂ) u * (C64.Kt t z - C64.Kt t zm)).re| ≤ ‖u‖ * (π * Real.exp (π * Y) * ρ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hz (by positivity))) (norm_nonneg _)
  rw [mul_sub, Complex.sub_re] at h2
  linarith [(abs_le.1 h2).2]

theorem im_le_of_disc {zm : ℂ} {z : CBall} (hz : memC P zm z) (ρ : ℕ) :
    ∀ ζ ∈ Metric.closedBall zm ((ρ : ℝ) / 2 ^ P), |ζ.im| ≤ ((z.im.absHi + ρ : ℕ) : ℝ) / 2 ^ P := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 : |w.im - zm.im| ≤ ‖w - zm‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have h2 := abs_le_absHi hz.2
  have : |w.im| ≤ |zm.im| + ‖w - zm‖ := by
    have := abs_sub_abs_le_abs_sub w.im zm.im; linarith
  push_cast; rw [add_div]; linarith

/-! ### Pieces -/

/-- Semantics of the data of a piece with midpoint value `zm`. -/
structure PieceOK (P : ℕ) (zm : ℂ) (pd : PieceD) : Prop where
  z : memC P zm pd.z
  ne : zm ≠ 0
  sz : memC P (C64.S zm) pd.sz
  s1 : memC P (C64.S1 zm) pd.s1
  ls : ∀ ζ ∈ Metric.closedBall zm ((pd.rho : ℝ) / 2 ^ P), ‖C64.S1 ζ‖ ≤ (pd.ls : ℝ) / 2 ^ P
  eY : Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ P)) ≤ (pd.eY : ℝ) / 2 ^ P

theorem pieceD_ok {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {n0 n1 e : ℕ} {pd : PieceD}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ c.P) (h : pieceD c E n0 n1 e = some pd) :
    PieceOK c.P (C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))) pd ∧
    ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      ‖C64.ellipse cc a b q - C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))‖ ≤ (pd.rho : ℝ) / 2 ^ c.P := by
  unfold pieceD at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨z, hz, ρ, hρ, ⟨sz, s1⟩, hss, ls, hls, eY, heY, rfl⟩ := h
  have hzm := memC_ellPt hE (mem_midB he) hz
  obtain ⟨hne, hsz, hs1⟩ := memC_cSS1 hzm hss
  exact ⟨⟨hzm, hne, hsz, hs1, lsLoc_sound hzm hs1 hls, exp_le_expPiHi heY le_rfl⟩,
    fun q hq => ellRad_sound hE h01 he hρ hq⟩

/-- On the disc of a piece: `Re(ū S(w)) ≥ aLow / 2^P` and `Re(ū K_t(w)) ≤ Re(ū K_t(z_m)) + dP / 2^P`. -/
theorem disc_bounds {P : ℕ} {u zm : ℂ} {ub : CBall} {pd : PieceD} (hu : memC P u ub) (hpd : PieceOK P zm pd) {w : ℂ}
    (hw : ‖w - zm‖ ≤ (pd.rho : ℝ) / 2 ^ P) :
    (aLow P ub pd : ℝ) / 2 ^ P ≤ ((starRingEnd ℂ) u * C64.S w).re ∧
    ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), ((starRingEnd ℂ) u * C64.Kt t w).re ≤
      ((starRingEnd ℂ) u * C64.Kt t zm).re + (dPof P ub pd : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  set ρr : ℝ := (pd.rho : ℝ) / 2 ^ P
  have hnu := norm_le_normHi hu
  have hρ0 : 0 ≤ ρr := by positivity
  have hur : ‖u‖ * ρr ≤ (mulU P (normHi ub) pd.rho : ℝ) / 2 ^ P := mulU_le (norm_nonneg _) hρ0 hnu le_rfl
  have hL0 : 0 ≤ (pd.ls : ℝ) / 2 ^ P := by positivity
  constructor
  · have h1 := re_conj_S_ge (u := u) hw hpd.ls
    have h2 := (reConj_bounds hu hpd.sz).1
    have h3 : ‖u‖ * ((pd.ls : ℝ) / 2 ^ P * ρr) ≤ (mulU P (mulU P (normHi ub) pd.rho) pd.ls : ℝ) / 2 ^ P := by
      rw [show ‖u‖ * ((pd.ls : ℝ) / 2 ^ P * ρr) = (‖u‖ * ρr) * ((pd.ls : ℝ) / 2 ^ P) by ring]
      exact mulU_le (by positivity) hL0 hur le_rfl
    unfold aLow reConjLo at *
    push_cast
    rw [sub_div]
    linarith
  · intro t ht
    have h1 := re_conj_Kt_le (u := u) ht hw (im_le_of_disc hpd.z pd.rho)
    have hpi := pi_le_piHi (P := P)
    have hpe : π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ P)) ≤
        (mulU P (piHi P) pd.eY : ℝ) / 2 ^ P := mulU_le Real.pi_pos.le (Real.exp_pos _).le hpi hpd.eY
    have h3 : ‖u‖ * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ P)) * ρr) ≤
        (dPof P ub pd : ℝ) / 2 ^ P := by
      rw [show ‖u‖ * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ P)) * ρr) =
        (‖u‖ * ρr) * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ P))) by ring]
      exact mulU_le (by positivity) (by positivity) hur hpe
    linarith

/-- `⌊A τd / τn⌋ τ ≤ A` for `A > 0`, `τ = τn / τd`. -/
theorem floor_target_le {A : ℤ} (hA : 0 < A) {tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) :
    ((tn : ℝ) / td) * ((A.toNat * td / tn : ℕ) : ℝ) ≤ A := by
  have h1 : ((A.toNat * td / tn : ℕ) : ℝ) ≤ ((A.toNat * td : ℕ) : ℝ) / tn := Nat.cast_div_le
  have hA' : ((A.toNat : ℕ) : ℝ) = (A : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hA.le
  have htn' : (0 : ℝ) < tn := by exact_mod_cast htn
  have htd' : (0 : ℝ) < td := by exact_mod_cast htd
  calc ((tn : ℝ) / td) * ((A.toNat * td / tn : ℕ) : ℝ) ≤ ((tn : ℝ) / td) * (((A.toNat * td : ℕ) : ℝ) / tn) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = A := by push_cast; rw [hA']; field_simp

/-- The singleton term list of `Re(c K_t(ζ))`. -/
theorem fsum_single (c ζ : ℂ) (t : ℝ) : fsum [(c, ζ)] t = (c * C64.Kt t ζ).re := by simp [fsum]

/-! ### Type E arcs -/

/-- The E condition (Definition 6.6(ii)) at the parameter `s` of `T₁`. -/
def ECond (τ c a b : ℝ) (u : ℂ) (s : ℝ) : Prop :=
  0 < ((starRingEnd ℂ) u * C64.S (C64.ellipse c a b s)).re ∧
    ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), τ * ((starRingEnd ℂ) u * C64.Kt t (C64.ellipse c a b s)).re <
      ((starRingEnd ℂ) u * C64.S (C64.ellipse c a b s)).re

/-- From `tbound` with the target `tgt`: `τ Re(ū K_t(w)) < a` given `Re(ū K_t(w)) ≤ f + dP`, `f < tgt`. -/
theorem tgt_bound {tn td : ℕ} (htn : 0 < tn) (htd : 0 < td) {a : ℤ} (ha : 0 < a) {dP : ℕ} {P : ℕ} {x f : ℝ}
    (hx : x ≤ f + (dP : ℝ) / 2 ^ P) (hf : f < (tgt tn td a dP : ℝ) / 2 ^ P) :
    ((tn : ℝ) / td) * x < (a : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have hfl := floor_target_le ha htn htd
  have hτ : (0 : ℝ) < (tn : ℝ) / td := by
    have : (0 : ℝ) < tn := by exact_mod_cast htn
    have : (0 : ℝ) < td := by exact_mod_cast htd
    positivity
  unfold tgt at hf
  have e1 : ((((a.toNat * td / tn : ℕ) : ℤ) - (dP : ℤ) : ℤ) : ℝ) / 2 ^ P =
      ((a.toNat * td / tn : ℕ) : ℝ) / 2 ^ P - (dP : ℝ) / 2 ^ P := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_div]
  rw [e1] at hf
  have hx' : x < ((a.toNat * td / tn : ℕ) : ℝ) / 2 ^ P := by linarith
  calc ((tn : ℝ) / td) * x < ((tn : ℝ) / td) * (((a.toNat * td / tn : ℕ) : ℝ) / 2 ^ P) :=
        mul_lt_mul_of_pos_left hx' hτ
    _ = (((tn : ℝ) / td) * ((a.toNat * td / tn : ℕ) : ℝ)) / 2 ^ P := by ring
    _ ≤ (a : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hfl hP.le

theorem checkEPiece_ok {g : Glob} (hg : GlobOK g) {u : ℂ} {ub : CBall} (hu : memC g.P u ub) {n0 n1 e : ℕ}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ g.P) (h : checkEPiece g (T1B g) ub n0 n1 e = true) :
    ∀ s ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e), ECond g.tau.val g.c.val g.a.val g.b.val u s := by
  unfold checkEPiece at h
  simp only [Option.any_eq_true] at h
  obtain ⟨pd, hpd, T, hT, h⟩ := h
  unfold ePieceOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hA, htb⟩ := h
  have hP := two_pow_pos' g.P
  obtain ⟨hpdok, hrad⟩ := pieceD_ok (T1_ok hg) h01 he hpd
  have hTok := ptT_ok hpdok.z hg.D1 hg.hD hT
  have htb' := tbound_ok (czs := [((starRingEnd ℂ) u, C64.ellipse (g.c.val : ℂ) g.a.val g.b.val
      (((n0 : ℝ) + n1) / 2 ^ (e + 1)))]) htb
    (List.Forall₂.cons (termOf_ok hTok (C64Num.CBall.memC_conj hu)) List.Forall₂.nil)
    (by intro T' hT'; simp only [List.mem_singleton] at hT'; subst hT'; exact hTok.len)
  intro s hs
  obtain ⟨hS, hK⟩ := disc_bounds hu hpdok (hrad s hs)
  have hApos : (0 : ℝ) < (aLow g.P ub pd : ℝ) / 2 ^ g.P := div_pos (by exact_mod_cast hA) hP
  refine ⟨lt_of_lt_of_le hApos hS, fun t ht => ?_⟩
  have h2 := htb' t ht
  rw [fsum_single] at h2
  have htn : 0 < g.tau.n.toNat := by have := hg.tn; omega
  have htd : 0 < g.tau.d := by have := lt_trans hg.tn hg.tlt; omega
  rw [tau_eq hg]
  exact lt_of_lt_of_le (tgt_bound htn htd hA (hK t ht) h2) hS

theorem checkE_ok {g : Glob} (hg : GlobOK g) {u : ℂ} {ub : CBall} (hu : memC g.P u ub) :
    ∀ (fuel n0 n1 e : ℕ), n0 ≤ n1 → e + fuel + 1 ≤ g.P → checkE g (T1B g) ub fuel n0 n1 e = true →
    ∀ s ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e), ECond g.tau.val g.c.val g.a.val g.b.val u s
  | 0, n0, n1, e, h01, he, h => checkEPiece_ok hg hu h01 (by omega) h
  | fuel + 1, n0, n1, e, h01, he, h => by
    unfold checkE at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact checkEPiece_ok hg hu h01 (by omega) h
    · intro s hs
      have hm : ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) = ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; ring
      rcases le_total s (((n0 : ℝ) + n1) / 2 ^ (e + 1)) with hsm | hsm
      · refine checkE_ok hg hu fuel (2 * n0) (n0 + n1) (e + 1) (by omega) (by omega) h1 s ⟨?_, ?_⟩
        · push_cast; rw [pow_succ]
          have := hs.1; rw [show (2 * (n0 : ℝ)) / (2 ^ e * 2) = (n0 : ℝ) / 2 ^ e by field_simp]; exact this
        · rw [hm]; exact hsm
      · refine checkE_ok hg hu fuel (n0 + n1) (2 * n1) (e + 1) (by omega) (by omega) h2 s ⟨?_, ?_⟩
        · rw [hm]; exact hsm
        · push_cast; rw [pow_succ]
          have := hs.2; rw [show (2 * (n1 : ℝ)) / (2 ^ e * 2) = (n1 : ℝ) / 2 ^ e by field_simp]; exact this


theorem checkArcE_ok {g : Glob} (hg : GlobOK g) {s0 s1 : ℕ} {ur ui : ℤ} (h : checkArc g (.E s0 s1 ur ui) = true) :
    C64.ArcSettled g.tau.val g.c.val g.a.val g.b.val ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES) := by
  unfold checkArc at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h01, hE⟩ := h
  have := checkE_ok hg (memC_intC (P := g.P) (ur, ui)) g.dE s0 s1 g.ES h01.le (by have := hg.hE; omega) hE
  exact C64.settled_E (tau_pos hg).le (fun s hs => this s hs)

/-! ### The crossing radius -/

theorem rDisc_ok {g : Glob} (hg : GlobOK g) {tn td s0 s1 sc : ℕ} {zcB Sc S1c : CBall} {r : ℕ}
    (h0c : s0 ≤ sc) (hc1 : sc ≤ s1) (htd : 0 < td)
    (hzc : memC g.P (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) zcB)
    (hSc : memC g.P (C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))) Sc)
    (hS1c : memC g.P (C64.S1 (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))) S1c)
    (h : rDisc g (T1B g) tn td s0 s1 sc zcB Sc S1c = some r) :
    ∀ μ : MeasureTheory.Measure ℝ, C64.ClassA ((tn : ℝ) / td) μ →
      ∀ s ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES), ∀ lam ∈ Set.Ioc (0 : ℝ) 1,
      C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) =
        lam * C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) →
      ∃ σ : ℝ, 1 ≤ σ ∧ ‖C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) -
        (σ : ℂ) * C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))‖ ≤ (r : ℝ) / 2 ^ g.P := by
  set zc := C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)
  unfold rDisc at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨sp, hsp, L, hL, h⟩ := h
  split_ifs at h with hmS
  obtain ⟨eY, heY, rfl⟩ := Option.map_eq_some_iff.mp h
  set d := dOf g.P g.ES sp s0 s1 sc
  have hP := two_pow_pos' g.P
  have hpe := two_pow_pos' g.ES
  have hE1 := T1_ok hg
  have hEP : g.ES + 1 ≤ g.P := by have := hg.hE; omega
  -- |z(s) - z_c| ≤ d on the arc
  have hV : ∀ q ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES), spd g.a.val g.b.val q ≤
      (sp : ℝ) / 2 ^ (2 * g.P) := fun q hq => spd_le_ellSp hE1 hsp (mem_pieceB (le_trans h0c hc1) hEP hq)
  have hscm : (sc : ℝ) / 2 ^ g.ES ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES) :=
    ⟨div_le_div_of_nonneg_right (by exact_mod_cast h0c) hpe.le, div_le_div_of_nonneg_right (by exact_mod_cast hc1) hpe.le⟩
  have hd : ∀ s ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES),
      ‖C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s - zc‖ ≤ (d : ℝ) / 2 ^ g.P := by
    intro s hs
    have h1 := norm_ellipse_sub_le (c := (g.c.val : ℂ)) hV hs hscm
    have hds : |s - (sc : ℝ) / 2 ^ g.ES| ≤ ((max (s1 - sc) (sc - s0) : ℕ) : ℝ) / 2 ^ g.ES := by
      rw [abs_le]
      have h1' : ((s1 - sc : ℕ) : ℝ) ≤ ((max (s1 - sc) (sc - s0) : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
      have h2' : ((sc - s0 : ℕ) : ℝ) ≤ ((max (s1 - sc) (sc - s0) : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
      rw [Nat.cast_sub hc1] at h1'; rw [Nat.cast_sub h0c] at h2'
      obtain ⟨hs1, hs2⟩ := hs
      constructor
      · have : (s0 : ℝ) / 2 ^ g.ES - (sc : ℝ) / 2 ^ g.ES = -(((sc : ℝ) - s0) / 2 ^ g.ES) := by ring
        have h3 : ((sc : ℝ) - s0) / 2 ^ g.ES ≤ ((max (s1 - sc) (sc - s0) : ℕ) : ℝ) / 2 ^ g.ES :=
          div_le_div_of_nonneg_right h2' hpe.le
        linarith
      · have : (s1 : ℝ) / 2 ^ g.ES - (sc : ℝ) / 2 ^ g.ES = ((s1 : ℝ) - sc) / 2 ^ g.ES := by ring
        have h3 : ((s1 : ℝ) - sc) / 2 ^ g.ES ≤ ((max (s1 - sc) (sc - s0) : ℕ) : ℝ) / 2 ^ g.ES :=
          div_le_div_of_nonneg_right h1' hpe.le
        linarith
    have hpi := pi_le_piHi (P := g.P)
    have hc := cdiv_spec (2 * piHi g.P * sp * max (s1 - sc) (sc - s0)) (2 ^ (2 * g.P + g.ES)) (by positivity)
    push_cast at hc
    rw [← Nat.cast_max] at hc
    calc ‖C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s - zc‖
        ≤ 2 * π * ((sp : ℝ) / 2 ^ (2 * g.P)) * |s - (sc : ℝ) / 2 ^ g.ES| := h1
      _ ≤ 2 * ((piHi g.P : ℝ) / 2 ^ g.P) * ((sp : ℝ) / 2 ^ (2 * g.P)) *
          (((max (s1 - sc) (sc - s0) : ℕ) : ℝ) / 2 ^ g.ES) := by gcongr
      _ = (2 * (piHi g.P : ℝ) * sp * ((max (s1 - sc) (sc - s0) : ℕ) : ℝ)) / 2 ^ (2 * g.P + g.ES) / 2 ^ g.P := by
          rw [pow_add, pow_mul]; field_simp
      _ ≤ (d : ℝ) / 2 ^ g.P := div_le_div_of_nonneg_right hc hP.le
  have hLs : ∀ ζ ∈ Metric.closedBall zc ((d : ℝ) / 2 ^ g.P), ‖C64.S1 ζ‖ ≤ (L : ℝ) / 2 ^ g.P :=
    lsLoc_sound hzc hS1c hL
  have hY := im_le_of_disc hzc d
  have hmS' : (0 : ℝ) < (mSOf g.P Sc d L : ℝ) / 2 ^ g.P := div_pos (by exact_mod_cast hmS) hP
  have hSz : ∀ s ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES),
      (mSOf g.P Sc d L : ℝ) / 2 ^ g.P ≤ ‖C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s)‖ := by
    intro s hs
    have hzU : C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s ∈ Metric.closedBall zc ((d : ℝ) / 2 ^ g.P) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hd s hs
    have hcU : zc ∈ Metric.closedBall zc ((d : ℝ) / 2 ^ g.P) := Metric.mem_closedBall_self (by positivity)
    have h1 := C64.norm_sub_S_le (convex_closedBall zc _) hLs hzU hcU
    have h2 := normLo_le hSc
    have h3 : (L : ℝ) / 2 ^ g.P * ‖C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s - zc‖ ≤
        (mulU g.P d L : ℝ) / 2 ^ g.P := by
      rw [mul_comm]; exact mulU_le (norm_nonneg _) (by positivity) (hd s hs) le_rfl
    have h4 : ‖C64.S zc‖ - ‖C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) - C64.S zc‖ ≤
        ‖C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s)‖ := by
      have := norm_sub_norm_le (C64.S zc) (C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s))
      rw [norm_sub_rev (C64.S zc)] at this; linarith
    have h6 : ((mSOf g.P Sc d L : ℤ) : ℝ) / 2 ^ g.P =
        (normLo Sc : ℝ) / 2 ^ g.P - (mulU g.P d L : ℝ) / 2 ^ g.P := by
      unfold mSOf; push_cast; ring
    rw [h6]
    calc (normLo Sc : ℝ) / 2 ^ g.P - (mulU g.P d L : ℝ) / 2 ^ g.P
        ≤ ‖C64.S zc‖ - (L : ℝ) / 2 ^ g.P * ‖C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s - zc‖ := by linarith
      _ ≤ ‖C64.S zc‖ - ‖C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) - C64.S zc‖ := by linarith
      _ ≤ _ := h4
  -- the radius
  have hτ0 : (0 : ℝ) ≤ (tn : ℝ) / td := by positivity
  refine C64.hloc_of_bounds hτ0 hd hY hLs hmS' hSz ?_
  set Y := (((zcB.im.absHi + d : ℕ) : ℝ) / 2 ^ g.P)
  have he : Real.exp (π * Y) ≤ (eY : ℝ) / 2 ^ g.P := exp_le_expPiHi heY (le_refl Y)
  have hpi := pi_le_piHi (P := g.P)
  have htU : (tn : ℝ) / td ≤ (Ball.cdiv (tn * 2 ^ g.P) td : ℝ) / 2 ^ g.P := by
    have h' := cdiv_spec (tn * 2 ^ g.P) td htd
    push_cast at h'
    rw [le_div_iff₀ hP]
    calc (tn : ℝ) / td * 2 ^ g.P = (tn : ℝ) * 2 ^ g.P / td := by ring
      _ ≤ _ := h'
  have hA : π * ((tn : ℝ) / td) * Real.exp (π * Y) ≤
      (mulU g.P (piHi g.P) (mulU g.P (Ball.cdiv (tn * 2 ^ g.P) td) eY) : ℝ) / 2 ^ g.P := by
    rw [mul_assoc]
    exact mulU_le Real.pi_pos.le (by positivity) hpi (mulU_le hτ0 (Real.exp_pos _).le htU he)
  have hσ : (tn : ℝ) / td * Real.exp (π * Y) / ((mSOf g.P Sc d L : ℝ) / 2 ^ g.P) ≤
      (Ball.cdiv (tn * eY * 2 ^ g.P) (td * (mSOf g.P Sc d L).toNat) : ℝ) / 2 ^ g.P := by
    have hmpos : (0 : ℝ) < ((mSOf g.P Sc d L).toNat : ℝ) := by
      have : 0 < (mSOf g.P Sc d L).toNat := by omega
      exact_mod_cast this
    have hcast : (((mSOf g.P Sc d L).toNat : ℕ) : ℝ) = (mSOf g.P Sc d L : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hmS.le
    have h' := cdiv_spec (tn * eY * 2 ^ g.P) (td * (mSOf g.P Sc d L).toNat) (Nat.mul_pos htd (by omega))
    push_cast at h'
    rw [hcast] at h' hmpos
    have htd' : (0 : ℝ) < td := by exact_mod_cast htd
    calc (tn : ℝ) / td * Real.exp (π * Y) / ((mSOf g.P Sc d L : ℝ) / 2 ^ g.P)
        ≤ (tn : ℝ) / td * ((eY : ℝ) / 2 ^ g.P) / ((mSOf g.P Sc d L : ℝ) / 2 ^ g.P) := by gcongr
      _ = ((tn : ℝ) * eY * 2 ^ g.P / (td * (mSOf g.P Sc d L : ℝ))) / 2 ^ g.P := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right h' hP.le
  have hB : (tn : ℝ) / td * Real.exp (π * Y) / ((mSOf g.P Sc d L : ℝ) / 2 ^ g.P) * ((L : ℝ) / 2 ^ g.P) ≤
      (mulU g.P (Ball.cdiv (tn * eY * 2 ^ g.P) (td * (mSOf g.P Sc d L).toNat)) L : ℝ) / 2 ^ g.P :=
    mulU_le (by positivity) (by positivity) hσ le_rfl
  have hsum : π * ((tn : ℝ) / td) * Real.exp (π * Y) +
      (tn : ℝ) / td * Real.exp (π * Y) / ((mSOf g.P Sc d L : ℝ) / 2 ^ g.P) * ((L : ℝ) / 2 ^ g.P) ≤
      ((mulU g.P (piHi g.P) (mulU g.P (Ball.cdiv (tn * 2 ^ g.P) td) eY) +
        mulU g.P (Ball.cdiv (tn * eY * 2 ^ g.P) (td * (mSOf g.P Sc d L).toNat)) L : ℕ) : ℝ) / 2 ^ g.P := by
    push_cast; rw [add_div]; exact add_le_add hA hB
  unfold rOf
  exact mulU_le (by positivity) (by positivity) le_rfl hsum


/-- The checker's radius `max (rDisc ..) rX` is at least the proved radius, hence again valid. -/
theorem rBound_ok {g : Glob} (hg : GlobOK g) {tn td s0 s1 sc : ℕ} {zcB Sc S1c : CBall} {r : ℕ}
    (h0c : s0 ≤ sc) (hc1 : sc ≤ s1) (htd : 0 < td)
    (hzc : memC g.P (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) zcB)
    (hSc : memC g.P (C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))) Sc)
    (hS1c : memC g.P (C64.S1 (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))) S1c)
    {rX : ℕ} (h : rBound g (T1B g) tn td s0 s1 sc zcB Sc S1c rX = some r) :
    ∀ μ : MeasureTheory.Measure ℝ, C64.ClassA ((tn : ℝ) / td) μ →
      ∀ s ∈ Set.Icc ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES), ∀ lam ∈ Set.Ioc (0 : ℝ) 1,
      C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) =
        lam * C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val s) →
      ∃ σ : ℝ, 1 ≤ σ ∧ ‖C64.hat μ (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)) -
        (σ : ℂ) * C64.S (C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES))‖ ≤ (r : ℝ) / 2 ^ g.P := by
  unfold rBound at h
  obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  intro μ hμ s hs lam hlam hcr
  obtain ⟨σ, hσ, hb⟩ := rDisc_ok hg h0c hc1 htd hzc hSc hS1c h1 μ hμ s hs lam hlam hcr
  refine ⟨σ, hσ, hb.trans ?_⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_left r1 rX) (by positivity)

end C64Chk
