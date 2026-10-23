import C64.Num.Sound
import C64.Settle
import C64Core.Check

/-!
# Soundness of the checker, part 1: exact data, upper bounds, ellipses, `S` near a point
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Exact data -/

/-- The value of a rational datum. -/
noncomputable def Q.val (q : Q) : ℝ := (q.n : ℝ) / q.d

theorem mem_Qball {q : Q} (hq : 0 < q.d) : mem P q.val (q.ball P) := mem_ofRat P q.n q.d hq

theorem mem_dyB (n : ℤ) {e : ℕ} (he : e ≤ P) : mem P ((n : ℝ) / 2 ^ e) (dyB P n e) := by
  unfold dyB mem
  have h2 : (2 : ℝ) ^ P = 2 ^ (P - e) * 2 ^ e := by rw [← pow_add, Nat.sub_add_cancel he]
  have : ((n * ((2 ^ (P - e) : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P = (n : ℝ) / 2 ^ e := by
    push_cast; rw [h2]; field_simp
  simp only [this, sub_self, abs_zero, Nat.cast_zero, zero_div, le_refl]

/-- The complex number of an integer pair. -/
def cOf (x : ℤ × ℤ) : ℂ := ⟨x.1, x.2⟩

theorem memC_intC (x : ℤ × ℤ) : memC P (cOf x) (intC P x) := ⟨mem_ofInt P x.1, mem_ofInt P x.2⟩

/-! ### Upper bounds in units `2^-P` -/

theorem pi_le_piHi : π ≤ (piHi P : ℝ) / 2 ^ P := by
  have h := (mem_iff_lo_hi.1 (mem_piB P)).2
  have hpos : (0 : ℝ) < ((piB P).hi : ℝ) / 2 ^ P := lt_of_lt_of_le Real.pi_pos h
  have hhi : 0 ≤ (piB P).hi := by
    by_contra hc; push Not at hc
    have : ((piB P).hi : ℝ) < 0 := by exact_mod_cast hc
    have := div_neg_of_neg_of_pos this (two_pow_pos' P); linarith
  unfold piHi
  rw [show (((piB P).hi.toNat : ℕ) : ℝ) = ((piB P).hi : ℝ) by exact_mod_cast Int.toNat_of_nonneg hhi]
  exact h

theorem piHi_pos : (0 : ℝ) < (piHi P : ℝ) / 2 ^ P := lt_of_lt_of_le Real.pi_pos pi_le_piHi

theorem mulU_le {x y : ℝ} {X Y : ℕ} (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ (X : ℝ) / 2 ^ P)
    (hy : y ≤ (Y : ℝ) / 2 ^ P) : x * y ≤ (mulU P X Y : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  unfold mulU
  have hc := cdiv_spec (X * Y) (2 ^ P) (by positivity)
  push_cast at hc
  calc x * y ≤ ((X : ℝ) / 2 ^ P) * ((Y : ℝ) / 2 ^ P) := mul_le_mul hx hy hy0 (by positivity)
    _ = ((X : ℝ) * Y / 2 ^ P) / 2 ^ P := by ring
    _ ≤ (Ball.cdiv (X * Y) (2 ^ P) : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hc hP.le

theorem cdiv_le {x : ℝ} {X d : ℕ} (hd : 0 < d) (hx : x ≤ (X : ℝ) / 2 ^ P) :
    x / d ≤ (Ball.cdiv X d : ℝ) / 2 ^ P := by
  have hP := two_pow_pos' P
  have hc := cdiv_spec X d hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  calc x / d ≤ ((X : ℝ) / 2 ^ P) / d := div_le_div_of_nonneg_right hx hd'.le
    _ = ((X : ℝ) / d) / 2 ^ P := by ring
    _ ≤ (Ball.cdiv X d : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hc hP.le

theorem exp_le_expPiHi {c : Cfg} {Y E : ℕ} (h : expPiHi c Y = some E) {y : ℝ} (hy : y ≤ (Y : ℝ) / 2 ^ c.P) :
    Real.exp (π * y) ≤ (E : ℝ) / 2 ^ c.P := by
  unfold expPiHi at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hY : mem c.P ((Y : ℝ) / 2 ^ c.P) (⟨(Y : ℤ), 0⟩ : Ball) := by
    have := mem_point' c.P (Y : ℤ); push_cast at this; exact this
  have hm := mem_expB (mem_mul (mem_piB c.P) hY) he
  have h1 := (mem_iff_lo_hi.1 hm).2
  have hpos : (0 : ℝ) < (e.hi : ℝ) / 2 ^ c.P := lt_of_lt_of_le (Real.exp_pos _) h1
  have hhi : 0 ≤ e.hi := by
    by_contra hc; push Not at hc
    have : (e.hi : ℝ) < 0 := by exact_mod_cast hc
    have := div_neg_of_neg_of_pos this (two_pow_pos' c.P); linarith
  rw [show ((e.hi.toNat : ℕ) : ℝ) = (e.hi : ℝ) by exact_mod_cast Int.toNat_of_nonneg hhi]
  refine le_trans (Real.exp_le_exp.2 ?_) h1
  exact mul_le_mul_of_nonneg_left hy Real.pi_pos.le

theorem expPiHi_nonneg {c : Cfg} {Y E : ℕ} (h : expPiHi c Y = some E) : (0 : ℝ) ≤ (E : ℝ) / 2 ^ c.P := by
  have := exp_le_expPiHi h (y := 0) (by positivity)
  exact le_trans (Real.exp_pos _).le this

theorem reConj_bounds {u w : ℂ} {a b : CBall} (hu : memC P u a) (hw : memC P w b) :
    (reConjLo P a b : ℝ) / 2 ^ P ≤ ((starRingEnd ℂ) u * w).re ∧
      ((starRingEnd ℂ) u * w).re ≤ (reConjHi P a b : ℝ) / 2 ^ P := by
  have h := (C64Num.CBall.memC_mul (C64Num.CBall.memC_conj hu) hw).1
  exact mem_iff_lo_hi.1 h

theorem norm_le_normHi' {z : ℂ} {a : CBall} (ha : memC P z a) : ‖z‖ ≤ (normHi a : ℝ) / 2 ^ P :=
  norm_le_normHi ha

/-! ### Dyadic pieces -/

theorem mem_pieceB {n0 n1 e : ℕ} (h01 : n0 ≤ n1) (he : e + 1 ≤ P) {q : ℝ}
    (hq : q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e)) : mem P q (pieceB P n0 n1 e) := by
  unfold pieceB mem
  have hP := two_pow_pos' P
  have h2 : (2 : ℝ) ^ P = 2 ^ (P - (e + 1)) * 2 ^ (e + 1) := by rw [← pow_add, Nat.sub_add_cancel he]
  have e1 : ((((n0 + n1 : ℕ) : ℤ) * ((2 ^ (P - (e + 1)) : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P =
      ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; rw [h2]; field_simp
  have e2 : (((n1 - n0) * 2 ^ (P - (e + 1)) : ℕ) : ℝ) / 2 ^ P = ((n1 : ℝ) - n0) / 2 ^ (e + 1) := by
    rw [Nat.cast_mul, Nat.cast_sub h01]; push_cast; rw [h2]; field_simp
  rw [e1, e2, abs_le]
  obtain ⟨hq1, hq2⟩ := hq
  have k1 : (n0 : ℝ) / 2 ^ e = 2 * n0 / 2 ^ (e + 1) := by rw [pow_succ]; field_simp
  have k2 : (n1 : ℝ) / 2 ^ e = 2 * n1 / 2 ^ (e + 1) := by rw [pow_succ]; field_simp
  rw [k1] at hq1; rw [k2] at hq2
  constructor
  · have : -(((n1 : ℝ) - n0) / 2 ^ (e + 1)) = 2 * n0 / 2 ^ (e + 1) - (n0 + n1) / 2 ^ (e + 1) := by ring
    linarith
  · have : ((n1 : ℝ) - n0) / 2 ^ (e + 1) = 2 * n1 / 2 ^ (e + 1) - (n0 + n1) / 2 ^ (e + 1) := by ring
    linarith

theorem mem_midB {n0 n1 e : ℕ} (he : e + 1 ≤ P) :
    mem P (((n0 : ℝ) + n1) / 2 ^ (e + 1)) (midB P n0 n1 e) := by
  have := mem_dyB (P := P) ((n0 + n1 : ℕ) : ℤ) he
  push_cast at this; exact this

/-! ### Ellipses -/

/-- The balls of an ellipse contain its exact data. -/
structure EllOK (P : ℕ) (c : ℂ) (a b : ℝ) (E : EllB) : Prop where
  cr : mem P c.re E.cr
  ci : mem P c.im E.ci
  a : mem P a E.a
  b : mem P b E.b

theorem ellipse_re (c : ℂ) (a b s : ℝ) : (C64.ellipse c a b s).re = c.re + a * Real.cos (2 * π * s) := by
  simp only [C64.ellipse, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im]
  ring

theorem ellipse_im (c : ℂ) (a b s : ℝ) : (C64.ellipse c a b s).im = c.im + b * Real.sin (2 * π * s) := by
  simp only [C64.ellipse, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.ofReal_im,
    Complex.I_im]
  ring

theorem memC_ellPt {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {q : ℝ} {U : Ball}
    (hq : mem c.P q U) {z : CBall} (h : ellPt c E U = some z) : memC c.P (C64.ellipse cc a b q) z := by
  unfold ellPt at h
  obtain ⟨⟨co, si⟩, hcs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hx := mem_cosSinTurn hq hcs
  refine ⟨?_, ?_⟩
  · rw [ellipse_re]; exact mem_add hE.cr (mem_mul hE.a hx.1)
  · rw [ellipse_im]; exact mem_add hE.ci (mem_mul hE.b hx.2)

/-- Speed function: `|z'(s)| = 2π sp(s)`. -/
noncomputable def spd (a b s : ℝ) : ℝ := Real.sqrt (a ^ 2 * Real.sin (2 * π * s) ^ 2 + b ^ 2 * Real.cos (2 * π * s) ^ 2)

theorem spd_le_ellSp {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {U : Ball} {sp : ℕ}
    (h : ellSp c E U = some sp) {q : ℝ} (hq : mem c.P q U) : spd a b q ≤ (sp : ℝ) / 2 ^ (2 * c.P) := by
  unfold ellSp at h
  obtain ⟨⟨co, si⟩, hcs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hx := mem_cosSinTurnC hq hcs
  have hP := two_pow_pos' c.P
  have ha := abs_le_absHi hE.a
  have hb := abs_le_absHi hE.b
  have hs := abs_le_absHi hx.2
  have hc := abs_le_absHi hx.1
  set A := (E.a.absHi : ℝ); set B := (E.b.absHi : ℝ); set Sh := (si.absHi : ℝ); set Ch := (co.absHi : ℝ)
  have h1 : |a * Real.sin (2 * π * q)| ≤ A * Sh / 2 ^ (2 * c.P) := by
    rw [abs_mul, pow_mul, show ((2:ℝ) ^ 2) ^ c.P = 2 ^ c.P * 2 ^ c.P by rw [← mul_pow]; norm_num]
    calc |a| * |Real.sin (2 * π * q)| ≤ (A / 2 ^ c.P) * (Sh / 2 ^ c.P) :=
          mul_le_mul ha hs (abs_nonneg _) (by positivity)
      _ = A * Sh / (2 ^ c.P * 2 ^ c.P) := by ring
  have h2 : |b * Real.cos (2 * π * q)| ≤ B * Ch / 2 ^ (2 * c.P) := by
    rw [abs_mul, pow_mul, show ((2:ℝ) ^ 2) ^ c.P = 2 ^ c.P * 2 ^ c.P by rw [← mul_pow]; norm_num]
    calc |b| * |Real.cos (2 * π * q)| ≤ (B / 2 ^ c.P) * (Ch / 2 ^ c.P) :=
          mul_le_mul hb hc (abs_nonneg _) (by positivity)
      _ = B * Ch / (2 ^ c.P * 2 ^ c.P) := by ring
  have hQ : (0 : ℝ) < 2 ^ (2 * c.P) := by positivity
  unfold spd
  have hsq := sqrtHi_spec ((E.a.absHi * si.absHi) ^ 2 + (E.b.absHi * co.absHi) ^ 2)
  push_cast at hsq
  calc Real.sqrt (a ^ 2 * Real.sin (2 * π * q) ^ 2 + b ^ 2 * Real.cos (2 * π * q) ^ 2)
      ≤ Real.sqrt (((A * Sh) ^ 2 + (B * Ch) ^ 2) / (2 ^ (2 * c.P)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have f1 : a ^ 2 * Real.sin (2 * π * q) ^ 2 ≤ (A * Sh / 2 ^ (2 * c.P)) ^ 2 := by
          rw [show a ^ 2 * Real.sin (2 * π * q) ^ 2 = |a * Real.sin (2 * π * q)| ^ 2 by rw [sq_abs]; ring]
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have f2 : b ^ 2 * Real.cos (2 * π * q) ^ 2 ≤ (B * Ch / 2 ^ (2 * c.P)) ^ 2 := by
          rw [show b ^ 2 * Real.cos (2 * π * q) ^ 2 = |b * Real.cos (2 * π * q)| ^ 2 by rw [sq_abs]; ring]
          exact pow_le_pow_left₀ (abs_nonneg _) h2 2
        rw [add_div, ← div_pow, ← div_pow]
        linarith
    _ = Real.sqrt ((A * Sh) ^ 2 + (B * Ch) ^ 2) / 2 ^ (2 * c.P) := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hQ.le]
    _ ≤ (sqrtHi ((E.a.absHi * si.absHi) ^ 2 + (E.b.absHi * co.absHi) ^ 2) : ℝ) / 2 ^ (2 * c.P) :=
        div_le_div_of_nonneg_right hsq hQ.le

/-- The derivative of the ellipse. -/
theorem hasDerivAt_ellipse (c : ℂ) (a b s : ℝ) :
    HasDerivAt (C64.ellipse c a b)
      (((-(2 * π * a * Real.sin (2 * π * s))) : ℝ) + ((2 * π * b * Real.cos (2 * π * s) : ℝ) : ℂ) * Complex.I) s := by
  have h1 : HasDerivAt (fun s : ℝ => a * Real.cos (2 * π * s)) (-(2 * π * a * Real.sin (2 * π * s))) s := by
    have := ((Real.hasDerivAt_cos (2 * π * s)).comp s ((hasDerivAt_id s).const_mul (2 * π))).const_mul a
    convert this using 1; simp; ring
  have h2 : HasDerivAt (fun s : ℝ => b * Real.sin (2 * π * s)) (2 * π * b * Real.cos (2 * π * s)) s := by
    have := ((Real.hasDerivAt_sin (2 * π * s)).comp s ((hasDerivAt_id s).const_mul (2 * π))).const_mul b
    convert this using 1; simp; ring
  have h1c := h1.ofReal_comp
  have h2c := (h2.ofReal_comp).mul_const Complex.I
  have := (h1c.const_add c).add h2c
  unfold C64.ellipse
  convert this using 1

theorem norm_deriv_ellipse (c : ℂ) (a b s : ℝ) :
    ‖(((-(2 * π * a * Real.sin (2 * π * s))) : ℝ) : ℂ) + ((2 * π * b * Real.cos (2 * π * s) : ℝ) : ℂ) * Complex.I‖ =
      2 * π * spd a b s := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.add_im, Complex.mul_im]
  unfold spd
  rw [show (2 * π * Real.sqrt (a ^ 2 * Real.sin (2 * π * s) ^ 2 + b ^ 2 * Real.cos (2 * π * s) ^ 2)) =
      Real.sqrt ((2 * π) ^ 2 * (a ^ 2 * Real.sin (2 * π * s) ^ 2 + b ^ 2 * Real.cos (2 * π * s) ^ 2)) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  congr 1; ring

/-- Mean value bound along the ellipse: `|z(q) - z(q')| ≤ 2π V |q - q'|` on an interval where `sp ≤ V`. -/
theorem norm_ellipse_sub_le {c : ℂ} {a b q0 q1 V : ℝ} (hV : ∀ s ∈ Set.Icc q0 q1, spd a b s ≤ V)
    {q q' : ℝ} (hq : q ∈ Set.Icc q0 q1) (hq' : q' ∈ Set.Icc q0 q1) :
    ‖C64.ellipse c a b q - C64.ellipse c a b q'‖ ≤ 2 * π * V * |q - q'| := by
  have := (convex_Icc q0 q1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := C64.ellipse c a b) (fun s _ => (hasDerivAt_ellipse c a b s).hasDerivWithinAt)
    (fun s hs => by rw [norm_deriv_ellipse c]; exact mul_le_mul_of_nonneg_left (hV s hs) (by positivity)) hq' hq
  rw [Real.norm_eq_abs] at this
  exact this

theorem ellRad_sound {c : Cfg} {cc : ℂ} {a b : ℝ} {E : EllB} (hE : EllOK c.P cc a b E) {n0 n1 e ρ : ℕ}
    (h01 : n0 ≤ n1) (he : e + 1 ≤ c.P) (h : ellRad c E n0 n1 e = some ρ) {q : ℝ}
    (hq : q ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e)) :
    ‖C64.ellipse cc a b q - C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))‖ ≤ (ρ : ℝ) / 2 ^ c.P := by
  unfold ellRad at h
  obtain ⟨sp, hsp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hP := two_pow_pos' c.P
  have hpe := two_pow_pos' e
  have hV : ∀ s ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e), spd a b s ≤ (sp : ℝ) / 2 ^ (2 * c.P) :=
    fun s hs => spd_le_ellSp hE hsp (mem_pieceB h01 he hs)
  have hm : ((n0 : ℝ) + n1) / 2 ^ (e + 1) ∈ Set.Icc ((n0 : ℝ) / 2 ^ e) ((n1 : ℝ) / 2 ^ e) := by
    have h01' : (n0 : ℝ) ≤ n1 := by exact_mod_cast h01
    rw [pow_succ]
    constructor
    · rw [div_le_div_iff₀ hpe (by positivity)]; nlinarith
    · rw [div_le_div_iff₀ (by positivity) hpe]; nlinarith
  have h1 := norm_ellipse_sub_le (c := cc) hV hq hm
  have hd : |q - ((n0 : ℝ) + n1) / 2 ^ (e + 1)| ≤ ((n1 : ℝ) - n0) / 2 ^ (e + 1) := by
    have := mem_pieceB (P := c.P) h01 he hq
    unfold pieceB mem at this
    have h2 : (2 : ℝ) ^ c.P = 2 ^ (c.P - (e + 1)) * 2 ^ (e + 1) := by rw [← pow_add, Nat.sub_add_cancel he]
    have e1 : ((((n0 + n1 : ℕ) : ℤ) * ((2 ^ (c.P - (e + 1)) : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ c.P =
        ((n0 : ℝ) + n1) / 2 ^ (e + 1) := by push_cast; rw [h2]; field_simp
    have e2 : (((n1 - n0) * 2 ^ (c.P - (e + 1)) : ℕ) : ℝ) / 2 ^ c.P = ((n1 : ℝ) - n0) / 2 ^ (e + 1) := by
      rw [Nat.cast_mul, Nat.cast_sub h01]; push_cast; rw [h2]; field_simp
    rwa [e1, e2] at this
  have hpi := pi_le_piHi (P := c.P)
  have hc := cdiv_spec (piHi c.P * sp * (n1 - n0)) (2 ^ (2 * c.P + e)) (by positivity)
  have hsub : ((n1 - n0 : ℕ) : ℝ) = (n1 : ℝ) - n0 := Nat.cast_sub h01
  push_cast [hsub] at hc
  calc ‖C64.ellipse cc a b q - C64.ellipse cc a b (((n0 : ℝ) + n1) / 2 ^ (e + 1))‖
      ≤ 2 * π * ((sp : ℝ) / 2 ^ (2 * c.P)) * |q - ((n0 : ℝ) + n1) / 2 ^ (e + 1)| := h1
    _ ≤ 2 * ((piHi c.P : ℝ) / 2 ^ c.P) * ((sp : ℝ) / 2 ^ (2 * c.P)) * (((n1 : ℝ) - n0) / 2 ^ (e + 1)) := by
        gcongr
    _ = (piHi c.P : ℝ) * sp * ((n1 : ℝ) - n0) / 2 ^ (2 * c.P + e) / 2 ^ c.P := by
        rw [pow_succ, pow_add, pow_mul]; field_simp
    _ ≤ (Ball.cdiv (piHi c.P * sp * (n1 - n0)) (2 ^ (2 * c.P + e)) : ℝ) / 2 ^ c.P :=
        div_le_div_of_nonneg_right hc hP.le

/-! ### `S` near a point -/

theorem lsLoc_sound {c : Cfg} {z0 : ℂ} {z s1 : CBall} {ρ L : ℕ} (hz : memC c.P z0 z) (hs1 : memC c.P (C64.S1 z0) s1)
    (h : lsLoc c z s1 ρ = some L) :
    ∀ ζ ∈ Metric.closedBall z0 ((ρ : ℝ) / 2 ^ c.P), ‖C64.S1 ζ‖ ≤ (L : ℝ) / 2 ^ c.P := by
  intro ζ hζ
  unfold lsLoc at h
  obtain ⟨eY, heY, rfl⟩ := Option.map_eq_some_iff.mp h
  have hP := two_pow_pos' c.P
  set Y : ℝ := ((z.im.absHi + ρ : ℕ) : ℝ) / 2 ^ c.P
  have hY : ∀ w ∈ Metric.closedBall z0 ((ρ : ℝ) / 2 ^ c.P), |w.im| ≤ Y := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 : |w.im - z0.im| ≤ ‖w - z0‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h2 := abs_le_absHi hz.2
    have : |w.im| ≤ |z0.im| + ‖w - z0‖ := by
      have := abs_sub_abs_le_abs_sub w.im z0.im; linarith
    simp only [Y]; push_cast; rw [add_div]; linarith
  have h1 := C64.norm_S1_le_disc hζ hY
  have hn := norm_le_normHi hs1
  have he := exp_le_expPiHi heY (le_refl Y)
  have hpi := pi_le_piHi (P := c.P)
  have hρ : (0 : ℝ) ≤ (ρ : ℝ) / 2 ^ c.P := by positivity
  have hc := cdiv_spec (piHi c.P ^ 2 * eY * ρ) (3 * 2 ^ (3 * c.P)) (by positivity)
  push_cast at hc
  calc ‖C64.S1 ζ‖ ≤ ‖C64.S1 z0‖ + (ρ : ℝ) / 2 ^ c.P * (π ^ 2 / 3 * Real.exp (π * Y)) := h1
    _ ≤ (normHi s1 : ℝ) / 2 ^ c.P + (ρ : ℝ) / 2 ^ c.P *
          (((piHi c.P : ℝ) / 2 ^ c.P) ^ 2 / 3 * ((eY : ℝ) / 2 ^ c.P)) := by
        gcongr
    _ = (normHi s1 : ℝ) / 2 ^ c.P + ((piHi c.P : ℝ) ^ 2 * eY * ρ / (3 * 2 ^ (3 * c.P))) / 2 ^ c.P := by
        rw [show (2 : ℝ) ^ (3 * c.P) = (2 ^ c.P) ^ 3 by rw [← pow_mul, mul_comm]]; field_simp
    _ ≤ (normHi s1 : ℝ) / 2 ^ c.P + (Ball.cdiv (piHi c.P ^ 2 * eY * ρ) (3 * 2 ^ (3 * c.P)) : ℝ) / 2 ^ c.P := by
        gcongr
    _ = ((normHi s1 + Ball.cdiv (piHi c.P ^ 2 * eY * ρ) (3 * 2 ^ (3 * c.P)) : ℕ) : ℝ) / 2 ^ c.P := by
        push_cast; ring

end C64Chk
