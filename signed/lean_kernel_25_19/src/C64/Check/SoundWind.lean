import C64.Check.SoundWit

/-!
# Soundness of the checker, part 6: atoms of witness measures, winding numbers by half-plane labels
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Atoms -/

/-- The atoms `(t_k, m_k)` of a witness measure: `t_k ∈ [-1/2, 1/2]`, `m_k ≥ 0`, positive denominators. -/
def AtomsOK (as : List (Q × Q)) : Prop :=
  ∀ a ∈ as, 0 < a.1.d ∧ |a.1.val| ≤ 1 / 2 ∧ 0 < a.2.d ∧ 0 ≤ a.2.val

/-- `Σ m_k`. -/
noncomputable def msum (as : List (Q × Q)) : ℝ := (as.map fun a => a.2.val).sum

theorem atomsOK_ok : ∀ (as : List (Q × Q)) {mn : ℤ} {md : ℕ}, atomsOK as = some (mn, md) →
    AtomsOK as ∧ 0 < md ∧ msum as = (mn : ℝ) / md
  | [], mn, md, h => by
    simp only [atomsOK, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun a ha => by simp at ha, by norm_num, by simp [msum]⟩
  | (t, m) :: as, mn, md, h => by
    unfold atomsOK at h
    split_ifs at h with hc
    obtain ⟨⟨mn', md'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hA, hmd, hs⟩ := atomsOK_ok as h'
    obtain ⟨htd, htn, hmd0, hmn⟩ := hc
    have htd' : (0 : ℝ) < t.d := by exact_mod_cast htd
    have hmd0' : (0 : ℝ) < m.d := by exact_mod_cast hmd0
    have hmd' : (0 : ℝ) < md' := by exact_mod_cast hmd
    refine ⟨fun a ha => ?_, Nat.mul_pos hmd0 hmd, ?_⟩
    · simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · refine ⟨htd, ?_, hmd0, ?_⟩
        · unfold Q.val
          rw [abs_div, abs_of_pos htd', div_le_iff₀ htd']
          have : (2 * t.n.natAbs : ℝ) ≤ t.d := by exact_mod_cast htn
          have e : |(t.n : ℝ)| = (t.n.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
          rw [e]; linarith
        · unfold Q.val; exact div_nonneg (by exact_mod_cast hmn) hmd0'.le
      · exact hA a ha
    · simp only [msum, List.map_cons, List.sum_cons] at hs ⊢
      rw [hs]; unfold Q.val; push_cast; field_simp

/-- `Σ m_k K_{t_k}(z)`. -/
noncomputable def wsum (as : List (Q × Q)) (z : ℂ) : ℂ := (as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z).sum

theorem sumK_ok {c : Cfg} {z : ℂ} {zb : CBall} (hz : memC c.P z zb) : ∀ (as : List (Q × Q)) {w : CBall},
    (∀ a ∈ as, 0 < a.1.d ∧ 0 < a.2.d) → sumK c zb as = some w → memC c.P (wsum as z) w
  | [], w, _, h => by
    simp only [sumK, Option.some.injEq] at h; subst h
    exact ⟨by simp [wsum, mem], by simp [wsum, mem]⟩
  | (t, m) :: as, w, hd, h => by
    unfold sumK at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, s, hs, rfl⟩ := h
    have hd0 := hd (t, m) (by simp)
    have hK := memC_ckt (mem_Qball hd0.1) hz hk
    have hS := sumK_ok hz as (fun a ha => hd a (by simp [ha])) hs
    have := C64Num.CBall.memC_add (C64Num.CBall.memC_mulR (mem_Qball hd0.2) hK) hS
    simpa [wsum] using this

theorem continuous_wsum (as : List (Q × Q)) : Continuous (wsum as) := by
  unfold wsum
  induction as with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_const.mul (C64.continuous_Kt _)).add ih

theorem norm_wsum_sub_le {as : List (Q × Q)} (hA : AtomsOK as) {U : Set ℂ} (hU : Convex ℝ U) {Y : ℝ}
    (hY : ∀ ζ ∈ U, |ζ.im| ≤ Y) {z z' : ℂ} (hz : z ∈ U) (hz' : z' ∈ U) :
    ‖wsum as z - wsum as z'‖ ≤ msum as * (π * Real.exp (π * Y) * ‖z - z'‖) := by
  induction as with
  | nil => simp [wsum, msum]
  | cons a as ih =>
    have ha := hA a (by simp)
    have ih' := ih (fun b hb => hA b (by simp [hb]))
    simp only [wsum, msum, List.map_cons, List.sum_cons] at ih' ⊢
    have ht : a.1.val ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
      have := abs_le.1 ha.2.1; constructor <;> linarith [this.1, this.2]
    have hK := C64.norm_sub_Kt_le ht hU hY hz hz'
    calc ‖(a.2.val : ℂ) * C64.Kt a.1.val z + (as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z).sum -
          ((a.2.val : ℂ) * C64.Kt a.1.val z' + (as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z').sum)‖
        = ‖(a.2.val : ℂ) * (C64.Kt a.1.val z - C64.Kt a.1.val z') +
            ((as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z).sum -
              (as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z').sum)‖ := by ring_nf
      _ ≤ ‖(a.2.val : ℂ) * (C64.Kt a.1.val z - C64.Kt a.1.val z')‖ +
            ‖(as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z).sum -
              (as.map fun a => (a.2.val : ℂ) * C64.Kt a.1.val z').sum‖ := norm_add_le _ _
      _ ≤ a.2.val * (π * Real.exp (π * Y) * ‖z - z'‖) +
            (as.map fun a => a.2.val).sum * (π * Real.exp (π * Y) * ‖z - z'‖) := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.2.2.2]
          exact mul_le_mul_of_nonneg_left hK ha.2.2.2
      _ = _ := by ring

/-! ### Half-plane labels -/

theorem HP_iff (h : ℕ) (w : ℂ) (hh : h < 4) :
    C64.HP h w ↔ (h = 0 ∧ 0 < w.re) ∨ (h = 1 ∧ 0 < w.im) ∨ (h = 2 ∧ 0 < -w.re) ∨ (h = 3 ∧ 0 < -w.im) := by
  unfold C64.HP
  interval_cases h <;> simp [pow_succ, Complex.mul_re]

theorem label_ok {gm : CBall} {thr : ℤ} {h : ℕ} {g : ℂ} (hg : memC P g gm) (hl : label gm thr = some h) :
    h < 4 ∧ ∀ w : ℂ, ‖w - g‖ ≤ (thr : ℝ) / 2 ^ P → C64.HP h w := by
  have hP := two_pow_pos' P
  have hre := mem_iff_lo_hi.1 hg.1
  have him := mem_iff_lo_hi.1 hg.2
  have bre : ∀ w : ℂ, |w.re - g.re| ≤ ‖w - g‖ := fun w => by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have bim : ∀ w : ℂ, |w.im - g.im| ≤ ‖w - g‖ := fun w => by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  unfold label at hl
  split_ifs at hl with h0 h1 h2 h3 <;> simp only [Option.some.injEq] at hl <;> subst hl
  · refine ⟨by norm_num, fun w hw => (HP_iff 0 w (by norm_num)).2 (Or.inl ⟨rfl, ?_⟩)⟩
    have : (thr : ℝ) < gm.re.lo := by exact_mod_cast h0
    have h' : (thr : ℝ) / 2 ^ P < (gm.re.lo : ℝ) / 2 ^ P := div_lt_div_of_pos_right this hP
    have := bre w; have := (abs_le.1 this).1; linarith [hre.1]
  · refine ⟨by norm_num, fun w hw => (HP_iff 1 w (by norm_num)).2 (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
    have : (thr : ℝ) < gm.im.lo := by exact_mod_cast h1
    have h' : (thr : ℝ) / 2 ^ P < (gm.im.lo : ℝ) / 2 ^ P := div_lt_div_of_pos_right this hP
    have := bim w; have := (abs_le.1 this).1; linarith [him.1]
  · refine ⟨by norm_num, fun w hw => (HP_iff 2 w (by norm_num)).2 (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩)))⟩
    have : (gm.re.hi : ℝ) + thr < 0 := by exact_mod_cast h2
    have h' : (gm.re.hi : ℝ) / 2 ^ P + (thr : ℝ) / 2 ^ P < 0 := by rw [← add_div]; exact div_neg_of_neg_of_pos this hP
    have := bre w; have := (abs_le.1 this).2; linarith [hre.2]
  · refine ⟨by norm_num, fun w hw => (HP_iff 3 w (by norm_num)).2 (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩)))⟩
    have : (gm.im.hi : ℝ) + thr < 0 := by exact_mod_cast h3
    have h' : (gm.im.hi : ℝ) / 2 ^ P + (thr : ℝ) / 2 ^ P < 0 := by rw [← add_div]; exact div_neg_of_neg_of_pos this hP
    have := bim w; have := (abs_le.1 this).2; linarith [him.2]


/-! ### Labelled pieces -/

theorem windPiece_ok {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hm : msum as ≤ (mSum : ℝ) / 2 ^ c.P) {n0 n1 e h : ℕ} (h01 : n0 ≤ n1)
    (he : e + 1 ≤ c.P) (hw : windPiece c E as mSum n0 n1 e = some h) :
    h < 4 ∧ ∀ q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e),
      C64.HP h (C64.S (C64.ellipse cc a b q) - wsum as (C64.ellipse cc a b q)) := by
  unfold windPiece at hw
  simp only [Option.bind_eq_some_iff] at hw
  obtain ⟨pd, hpd, wk, hwk, hl⟩ := hw
  obtain ⟨hpdok, hrad⟩ := pieceD_ok hE h01 he hpd
  have hwk' := sumK_ok hpdok.z as (fun x hx => ⟨(hA x hx).1, (hA x hx).2.2.1⟩) hwk
  have hg := C64Num.CBall.memC_sub hpdok.sz hwk'
  obtain ⟨h4, hHP⟩ := label_ok hg hl
  refine ⟨h4, fun q hq => hHP _ ?_⟩
  set pm := C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))
  set p := C64.ellipse cc a b q
  have hP := two_pow_pos' c.P
  set ρr : ℝ := (pd.rho : ℝ) / 2 ^ c.P
  have hd : ‖p - pm‖ ≤ ρr := hrad q hq
  have hpU : p ∈ Metric.closedBall pm ρr := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hd
  have hcU : pm ∈ Metric.closedBall pm ρr := Metric.mem_closedBall_self ((norm_nonneg _).trans hd)
  have h1 := C64.norm_sub_S_le (convex_closedBall pm ρr) hpdok.ls hpU hcU
  have h2 := norm_wsum_sub_le hA (convex_closedBall pm ρr) (im_le_of_disc hpdok.z pd.rho) hpU hcU
  have hms0 : 0 ≤ msum as := by
    unfold msum; exact List.sum_nonneg (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact (hA y hy).2.2.2)
  have hpi := pi_le_piHi (P := c.P)
  have hpe : π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P)) ≤
      (mulU c.P (piHi c.P) pd.eY : ℝ) / 2 ^ c.P := mulU_le Real.pi_pos.le (Real.exp_pos _).le hpi hpdok.eY
  have hmp : msum as * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P))) ≤
      (mulU c.P mSum (mulU c.P (piHi c.P) pd.eY) : ℝ) / 2 ^ c.P := mulU_le hms0 (by positivity) hm hpe
  have hsum : (pd.ls : ℝ) / 2 ^ c.P + msum as * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P))) ≤
      ((pd.ls + mulU c.P mSum (mulU c.P (piHi c.P) pd.eY) : ℕ) : ℝ) / 2 ^ c.P := by
    have e : ((pd.ls + mulU c.P mSum (mulU c.P (piHi c.P) pd.eY) : ℕ) : ℝ) / 2 ^ c.P =
        (pd.ls : ℝ) / 2 ^ c.P + (mulU c.P mSum (mulU c.P (piHi c.P) pd.eY) : ℝ) / 2 ^ c.P := by
      rw [Nat.cast_add (pd.ls) (mulU c.P mSum (mulU c.P (piHi c.P) pd.eY)), add_div]
    rw [e]; linarith
  have htot := mulU_le (by positivity) (by positivity) hsum (le_refl ((pd.rho : ℝ) / 2 ^ c.P))
  rw [Int.cast_natCast]
  calc ‖C64.S p - wsum as p - (C64.S pm - wsum as pm)‖
      = ‖(C64.S p - C64.S pm) - (wsum as p - wsum as pm)‖ := by ring_nf
    _ ≤ ‖C64.S p - C64.S pm‖ + ‖wsum as p - wsum as pm‖ := norm_sub_le _ _
    _ ≤ (pd.ls : ℝ) / 2 ^ c.P * ‖p - pm‖ +
          msum as * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P)) * ‖p - pm‖) :=
        add_le_add h1 h2
    _ = ((pd.ls : ℝ) / 2 ^ c.P + msum as * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P)))) *
          ‖p - pm‖ := by ring
    _ ≤ ((pd.ls : ℝ) / 2 ^ c.P + msum as * (π * Real.exp (π * (((pd.z.im.absHi + pd.rho : ℕ) : ℝ) / 2 ^ c.P)))) *
          ρr := mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ _ := htot

theorem orElse_eq_some' {α : Type} {o : Option α} {f : Unit → Option α} {a : α} (h : o.orElse f = some a) :
    o = some a ∨ (o = none ∧ f () = some a) := by
  cases o with
  | none => exact Or.inr ⟨rfl, by simpa using h⟩
  | some x => exact Or.inl (by simpa using h)

theorem jmpI_eq (h h' : ℕ) : jmpI h h' = C64.jmp h h' := rfl

theorem wind_ok {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {as : List (Q × Q)}
    (hA : AtomsOK as) {mSum : ℕ} (hm : msum as ≤ (mSum : ℝ) / 2 ^ c.P) :
    ∀ (fuel skip n0 n1 e : ℕ) (r : ℕ × ℕ × ℤ), n0 ≤ n1 → e + fuel ≤ c.P →
    wind c E as mSum fuel skip n0 n1 e = some r →
    C64.LabLC (fun q => C64.S (C64.ellipse cc a b q) - wsum as (C64.ellipse cc a b q))
      ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e) r.1 r.2.1 r.2.2
  | 0, _, _, _, _, _, _, _, h => by simp [wind] at h
  | fuel + 1, skip, n0, n1, e, r, h01, he, h => by
    rw [wind] at h
    have hpe := two_pow_pos' e
    have hab : (n0 : ℝ) / 2 ^ e ≤ (n1 : ℝ) / 2 ^ e :=
      div_le_div_of_nonneg_right (by exact_mod_cast h01) hpe.le
    rcases orElse_eq_some' h with h1 | ⟨_, h2⟩
    · obtain ⟨hh, hX, rfl⟩ := Option.map_eq_some_iff.mp h1
      by_cases hs : skip = 0
      · rw [if_pos hs] at hX
        obtain ⟨h4, hHP⟩ := windPiece_ok hE hA hm h01 (by omega) hX
        refine C64.LabLC.piece hab ?_ h4 hHP
        exact ((C64.continuous_S.comp (C64.continuous_ellipse cc a b)).sub
          ((continuous_wsum as).comp (C64.continuous_ellipse cc a b))).continuousOn
      · rw [if_neg hs] at hX; exact absurd hX (by simp)
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h2
      obtain ⟨r1, hr1, r2, hr2, rfl⟩ := h2
      have i1 := wind_ok hE hA hm fuel (skip - 1) (2 * n0) (n0 + n1) (e + 1) r1 (by omega) (by omega) hr1
      have i2 := wind_ok hE hA hm fuel (skip - 1) (n0 + n1) (2 * n1) (e + 1) r2 (by omega) (by omega) hr2
      have e0 : ((2 * n0 : ℕ) : ℝ) / 2 ^ (e + 1) = (n0 : ℝ) / 2 ^ e := by push_cast; rw [pow_succ]; field_simp
      have e1 : ((2 * n1 : ℕ) : ℝ) / 2 ^ (e + 1) = (n1 : ℝ) / 2 ^ e := by push_cast; rw [pow_succ]; field_simp
      rw [e0] at i1; rw [e1] at i2
      have hm1 : (n0 : ℝ) / 2 ^ e ≤ ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) := by
        rw [← e0]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : 2 * n0 ≤ n0 + n1)) (by positivity)
      have hm2 : ((n0 + n1 : ℕ) : ℝ) / 2 ^ (e + 1) ≤ (n1 : ℝ) / 2 ^ e := by
        rw [← e1]; exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : n0 + n1 ≤ 2 * n1)) (by positivity)
      have := C64.LabLC.comb hm1 hm2 i1 i2
      simpa [jmpI_eq] using this

theorem windOdd_ok {g : Glob} (hg : GlobOK g) {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK g.P cc a b E)
    {as : List (Q × Q)} (hA : AtomsOK as) {mSum : ℕ} (hm : msum as ≤ (mSum : ℝ) / 2 ^ g.P)
    (h : windOdd g E as mSum = true) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, C64.S (C64.ellipse cc a b q) - wsum as (C64.ellipse cc a b q) ≠ 0) ∧
    ∃ n : ℤ, Odd n ∧ C64.HasWinding (fun q => C64.S (C64.ellipse cc a b q) - wsum as (C64.ellipse cc a b q)) n := by
  unfold windOdd at h
  simp only [Option.any_eq_true, beq_iff_eq] at h
  obtain ⟨r, hr, hodd⟩ := h
  have hL := wind_ok (c := g.cfg) hE hA hm (g.dW + 1) 6 0 1 0 r (by norm_num) (by have := hg.hW; simp [Glob.cfg]; omega) hr
  simp only [Nat.cast_zero, Nat.cast_one, pow_zero, div_one] at hL
  have hper : C64.S (C64.ellipse cc a b 0) - wsum as (C64.ellipse cc a b 0) =
      C64.S (C64.ellipse cc a b 1) - wsum as (C64.ellipse cc a b 1) := by rw [C64.ellipse_zero_eq_one]
  refine ⟨fun q hq => ?_, r.2.2 + C64.jmp r.2.1 r.1, ?_, C64.LabLC.close hL hper⟩
  · obtain ⟨_, _, _, _, L, _, hexp, _⟩ := hL
    have h1 : Complex.exp (L q) = C64.S (C64.ellipse cc a b q) - wsum as (C64.ellipse cc a b q) := hexp q hq
    rw [← h1]; exact Complex.exp_ne_zero _
  · rw [← jmpI_eq, Int.odd_iff]; exact hodd

end C64Chk
