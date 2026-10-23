import C64Core.Num
import C64.Ival.Sound
import C64.Ival.SoundTrig
import C64.SDeriv

/-!
# Soundness of the complex balls and the function enclosures of `C64.Num.Core`
-/

namespace C64Num

open Ival Ival.Ball Real

variable {P : ℕ}

/-- `z` lies in the complex ball `w` at precision `P`. -/
def memC (P : ℕ) (z : ℂ) (w : CBall) : Prop := mem P z.re w.re ∧ mem P z.im w.im

namespace CBall

theorem memC_add {z w : ℂ} {a b : CBall} (ha : memC P z a) (hb : memC P w b) : memC P (z + w) (add a b) :=
  ⟨by rw [Complex.add_re]; exact mem_add ha.1 hb.1, by rw [Complex.add_im]; exact mem_add ha.2 hb.2⟩

theorem memC_sub {z w : ℂ} {a b : CBall} (ha : memC P z a) (hb : memC P w b) : memC P (z - w) (sub a b) :=
  ⟨by rw [Complex.sub_re]; exact mem_sub ha.1 hb.1, by rw [Complex.sub_im]; exact mem_sub ha.2 hb.2⟩

theorem memC_neg {z : ℂ} {a : CBall} (ha : memC P z a) : memC P (-z) (neg a) :=
  ⟨by rw [Complex.neg_re]; exact mem_neg ha.1, by rw [Complex.neg_im]; exact mem_neg ha.2⟩

theorem memC_conj {z : ℂ} {a : CBall} (ha : memC P z a) : memC P ((starRingEnd ℂ) z) (conj a) :=
  ⟨by rw [Complex.conj_re]; exact ha.1, by rw [Complex.conj_im]; exact mem_neg ha.2⟩

theorem memC_mul {z w : ℂ} {a b : CBall} (ha : memC P z a) (hb : memC P w b) : memC P (z * w) (mul P a b) :=
  ⟨by rw [Complex.mul_re]; exact mem_sub (mem_mul ha.1 hb.1) (mem_mul ha.2 hb.2),
   by rw [Complex.mul_im]; exact mem_add (mem_mul ha.1 hb.2) (mem_mul ha.2 hb.1)⟩

theorem memC_mulR {x : ℝ} {z : ℂ} {X : Ball} {a : CBall} (hx : mem P x X) (ha : memC P z a) :
    memC P ((x : ℂ) * z) (mulR P X a) :=
  ⟨by rw [Complex.re_ofReal_mul]; exact mem_mul hx ha.1, by rw [Complex.im_ofReal_mul]; exact mem_mul hx ha.2⟩

theorem memC_ofRat (P : ℕ) (a : ℤ) (b : ℕ) (c : ℤ) (d : ℕ) (hb : 0 < b) (hd : 0 < d) :
    memC P (⟨(a : ℝ) / b, (c : ℝ) / d⟩ : ℂ) (ofRat P a b c d) :=
  ⟨mem_ofRat P a b hb, mem_ofRat P c d hd⟩

end CBall

open CBall

/-! ### Norm bounds -/

theorem sqrtHi_spec (n : ℕ) : Real.sqrt n ≤ sqrtHi n := by
  unfold sqrtHi
  rw [Real.sqrt_le_left (by positivity)]
  have := Nat.lt_succ_sqrt' n
  push_cast
  exact_mod_cast this.le

theorem norm_le_normHi {z : ℂ} {a : CBall} (ha : memC P z a) : ‖z‖ ≤ (normHi a : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have h1 := abs_le_absHi ha.1
  have h2 := abs_le_absHi ha.2
  rw [Complex.norm_eq_sqrt_sq_add_sq, le_div_iff₀ hP]
  have hs := sqrtHi_spec (a.re.absHi ^ 2 + a.im.absHi ^ 2)
  calc Real.sqrt (z.re ^ 2 + z.im ^ 2) * 2 ^ P = Real.sqrt ((z.re * 2 ^ P) ^ 2 + (z.im * 2 ^ P) ^ 2) := by
        rw [show (z.re * 2 ^ P) ^ 2 + (z.im * 2 ^ P) ^ 2 = (z.re ^ 2 + z.im ^ 2) * (2 ^ P) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hP.le]
    _ ≤ Real.sqrt ((a.re.absHi : ℝ) ^ 2 + (a.im.absHi : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have e1 : |z.re * 2 ^ P| ≤ a.re.absHi := by
          rw [abs_mul, abs_of_pos hP]; rwa [le_div_iff₀ hP] at h1
        have e2 : |z.im * 2 ^ P| ≤ a.im.absHi := by
          rw [abs_mul, abs_of_pos hP]; rwa [le_div_iff₀ hP] at h2
        nlinarith [sq_abs (z.re * 2 ^ P), sq_abs (z.im * 2 ^ P), abs_nonneg (z.re * 2 ^ P),
          abs_nonneg (z.im * 2 ^ P)]
    _ ≤ (normHi a : ℝ) := by unfold normHi; exact_mod_cast hs

theorem absLo_le {x : ℝ} {a : Ball} (ha : mem P x a) : (absLo a : ℝ) / 2 ^ P ≤ |x| := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold absLo
  unfold mem at ha
  rw [div_le_iff₀ hP]
  rcases le_total a.m.natAbs a.r with h | h
  · rw [Nat.sub_eq_zero_of_le h]; simp only [Nat.cast_zero]; positivity
  · rw [Nat.cast_sub h]
    have h1 : |(a.m : ℝ) / 2 ^ P| ≤ |x| + (a.r : ℝ) / 2 ^ P := by
      have := abs_sub_abs_le_abs_sub ((a.m : ℝ) / 2 ^ P) x
      rw [abs_sub_comm] at ha; linarith
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP, add_mul, div_mul_cancel₀ _ hP.ne'] at h1
    have : (a.m.natAbs : ℝ) = |(a.m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this]; linarith

theorem normLo_le {z : ℂ} {a : CBall} (ha : memC P z a) : (normLo a : ℝ) / 2 ^ P ≤ ‖z‖ := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have h1 := absLo_le ha.1
  have h2 := absLo_le ha.2
  rw [Complex.norm_eq_sqrt_sq_add_sq, div_le_iff₀ hP]
  have hsq : ((Nat.sqrt (absLo a.re ^ 2 + absLo a.im ^ 2) : ℕ) : ℝ) ^ 2 ≤ (absLo a.re : ℝ) ^ 2 + (absLo a.im : ℝ) ^ 2 := by
    exact_mod_cast Nat.sqrt_le' (absLo a.re ^ 2 + absLo a.im ^ 2)
  have e1 : (absLo a.re : ℝ) ≤ |z.re| * 2 ^ P := by rwa [div_le_iff₀ hP] at h1
  have e2 : (absLo a.im : ℝ) ≤ |z.im| * 2 ^ P := by rwa [div_le_iff₀ hP] at h2
  unfold normLo
  calc ((Nat.sqrt (absLo a.re ^ 2 + absLo a.im ^ 2) : ℕ) : ℝ)
      ≤ Real.sqrt ((absLo a.re : ℝ) ^ 2 + (absLo a.im : ℝ) ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ ≤ Real.sqrt ((z.re * 2 ^ P) ^ 2 + (z.im * 2 ^ P) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have f1 : (absLo a.re : ℝ) ^ 2 ≤ (z.re * 2 ^ P) ^ 2 :=
          (pow_le_pow_left₀ (Nat.cast_nonneg _) e1 2).trans (le_of_eq (by rw [mul_pow, sq_abs, ← mul_pow]))
        have f2 : (absLo a.im : ℝ) ^ 2 ≤ (z.im * 2 ^ P) ^ 2 :=
          (pow_le_pow_left₀ (Nat.cast_nonneg _) e2 2).trans (le_of_eq (by rw [mul_pow, sq_abs, ← mul_pow]))
        linarith
    _ = Real.sqrt (z.re ^ 2 + z.im ^ 2) * 2 ^ P := by
        rw [show (z.re * 2 ^ P) ^ 2 + (z.im * 2 ^ P) ^ 2 = (z.re ^ 2 + z.im ^ 2) * (2 ^ P) ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hP.le]

/-! ### Reciprocal and complex division -/

theorem recipPos_sound {x : ℝ} {a q : Ball} (ha : mem P x a) (h : recipPos P a = some q) :
    0 < x ∧ mem P x⁻¹ q := by
  unfold recipPos at h
  split_ifs at h with hr
  simp only [Option.some.injEq] at h
  subst h
  have hP := two_pow_pos' P
  have hm0 : 0 < a.m := lt_of_le_of_lt (Int.natCast_nonneg _) hr
  set M : ℕ := a.m.toNat with hM
  have hMm : (M : ℤ) = a.m := Int.toNat_of_nonneg hm0.le
  have hMr : a.r < M := by omega
  rw [mem_iff_lo_hi] at ha
  unfold lo hi at ha
  rw [← hMm] at ha
  push_cast at ha
  have hMr' : (a.r : ℝ) < M := by exact_mod_cast hMr
  have hx0 : 0 < x := lt_of_lt_of_le (div_pos (by linarith) hP) ha.1
  refine ⟨hx0, ?_⟩
  set N : ℕ := 2 ^ (2 * P)
  have hN : (N : ℝ) = 2 ^ P * 2 ^ P := by simp only [N]; push_cast; ring
  set lo := N / (M + a.r)
  set hi := Ball.cdiv N (M - a.r)
  have hpos1 : 0 < M + a.r := by omega
  have hpos2 : 0 < M - a.r := by omega
  have hlo : (lo : ℝ) ≤ (N : ℝ) / ((M + a.r : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hpos1)]; exact_mod_cast Nat.div_mul_le_self N (M + a.r)
  have hhi : (N : ℝ) / ((M - a.r : ℕ) : ℝ) ≤ hi := cdiv_spec N (M - a.r) hpos2
  have hsub : ((M - a.r : ℕ) : ℝ) = (M : ℝ) - a.r := by rw [Nat.cast_sub hMr.le]
  -- 1/x between 2^P/(M + r) and 2^P/(M - r)
  have hinv1 : x⁻¹ ≤ 2 ^ P / ((M : ℝ) - a.r) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hx0 (by linarith)]
    have := ha.1; rw [div_le_iff₀ hP] at this; linarith
  have hinv2 : 2 ^ P / ((M : ℝ) + a.r) ≤ x⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hx0]
    have := ha.2; rw [le_div_iff₀ hP] at this; linarith
  have hlohi : lo ≤ hi := by
    have h1 : (N : ℝ) / ((M + a.r : ℕ) : ℝ) ≤ (N : ℝ) / ((M - a.r : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hpos2) (by exact_mod_cast (by omega : M - a.r ≤ M + a.r))
    exact_mod_cast hlo.trans (h1.trans hhi)
  have hc : (lo + hi) / 2 ≤ hi := by omega
  rw [mem_iff_lo_hi]
  unfold Ball.lo Ball.hi
  simp only
  push_cast [Nat.cast_sub hc]
  constructor
  · -- (2c - hi)/2^P ≤ lo/2^P ≤ 2^P/(M + r) ≤ 1/x
    have h2c : (((lo + hi) / 2 : ℕ) : ℝ) * 2 ≤ (lo : ℝ) + hi := by exact_mod_cast Nat.div_mul_le_self (lo + hi) 2
    have e1 : (N : ℝ) / ((M + a.r : ℕ) : ℝ) / 2 ^ P = 2 ^ P / ((M : ℝ) + a.r) := by
      rw [hN]; push_cast; field_simp
    calc ((((lo + hi) / 2 : ℕ) : ℝ) - ((hi : ℝ) - (((lo + hi) / 2 : ℕ) : ℝ))) / 2 ^ P ≤ (lo : ℝ) / 2 ^ P := by
          apply div_le_div_of_nonneg_right _ hP.le; linarith
      _ ≤ (N : ℝ) / ((M + a.r : ℕ) : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hlo hP.le
      _ = 2 ^ P / ((M : ℝ) + a.r) := e1
      _ ≤ x⁻¹ := hinv2
  · have e2 : (N : ℝ) / ((M - a.r : ℕ) : ℝ) / 2 ^ P = 2 ^ P / ((M : ℝ) - a.r) := by
      rw [hN, hsub]; field_simp
    calc x⁻¹ ≤ 2 ^ P / ((M : ℝ) - a.r) := hinv1
      _ = (N : ℝ) / ((M - a.r : ℕ) : ℝ) / 2 ^ P := e2.symm
      _ ≤ (hi : ℝ) / 2 ^ P := div_le_div_of_nonneg_right hhi hP.le
      _ = ((((lo + hi) / 2 : ℕ) : ℝ) + ((hi : ℝ) - (((lo + hi) / 2 : ℕ) : ℝ))) / 2 ^ P := by ring_nf

theorem cdiv_sound {w z : ℂ} {a b c : CBall} (hw : memC P w a) (hz : memC P z b) (h : cdiv P a b = some c) :
    z ≠ 0 ∧ memC P (w / z) c := by
  unfold cdiv at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have hn2 : mem P (z.re * z.re + z.im * z.im) (Ball.add (Ball.mul P b.re b.re) (Ball.mul P b.im b.im)) :=
    mem_add (mem_mul hz.1 hz.1) (mem_mul hz.2 hz.2)
  obtain ⟨hpos, hinv⟩ := recipPos_sound hn2 hq
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  refine ⟨hz0, ?_⟩
  have e : w / z = (((z.re * z.re + z.im * z.im)⁻¹ : ℝ) : ℂ) * (w * (starRingEnd ℂ) z) := by
    rw [div_eq_mul_inv, Complex.inv_def, Complex.normSq_apply]; push_cast; try ring
  rw [e]
  exact memC_mulR hinv (memC_mul hw (memC_conj hz))

/-! ### `K_t`, `cos(πz)`, `sin(πz)`, `S`, `S'` -/

theorem Kt_eq (t : ℝ) (z : ℂ) : C64.Kt t z =
    ⟨Real.exp (2 * π * t * z.im) * Real.cos (2 * π * (t * z.re)),
     -(Real.exp (2 * π * t * z.im) * Real.sin (2 * π * (t * z.re)))⟩ := by
  unfold C64.Kt
  have hre : (-2 * π * Complex.I * t * z : ℂ).re = 2 * π * t * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : (-2 * π * Complex.I * t * z : ℂ).im = -(2 * π * (t * z.re)) := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  apply Complex.ext
  · rw [Complex.exp_re, hre, him, Real.cos_neg]
  · rw [Complex.exp_im, hre, him, Real.sin_neg]; ring

theorem memC_ckt {c : Cfg} {t : ℝ} {z : ℂ} {T : Ball} {a w : CBall} (ht : mem c.P t T) (hz : memC c.P z a)
    (h : ckt c T a = some w) : memC c.P (C64.Kt t z) w := by
  unfold ckt at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨e, he, ⟨co, si⟩, hcs, rfl⟩ := h
  have hex : mem c.P (2 * π * t * z.im) (Ball.mul c.P (Ball.mulInt 2 (Ball.mul c.P (piB c.P) T)) a.im) := by
    have := mem_mul (mem_mulInt 2 (mem_mul (mem_piB c.P) ht)) hz.2
    push_cast at this; convert this using 1; ring
  have hE := mem_expB hex he
  have hT := mem_cosSinTurn (mem_mul ht hz.1) hcs
  rw [Kt_eq]
  exact ⟨mem_mul hE hT.1, mem_neg (mem_mul hE hT.2)⟩

theorem mem_coshSinhPi {c : Cfg} {y : ℝ} {Y : Ball} {ch sh : Ball} (hy : mem c.P y Y)
    (h : coshSinhPi c Y = some (ch, sh)) : mem c.P (Real.cosh (π * y)) ch ∧ mem c.P (Real.sinh (π * y)) sh := by
  unfold coshSinhPi at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨ep, hep, em, hem, rfl, rfl⟩ := h
  have hpy := mem_mul (mem_piB c.P) hy
  have h1 := mem_expB hpy hep
  have h2 := mem_expB (mem_neg hpy) hem
  constructor
  · have := mem_shr 1 (mem_add h1 h2)
    rw [Real.cosh_eq]; simpa using this
  · have := mem_shr 1 (mem_sub h1 h2)
    rw [Real.sinh_eq]; simpa using this

theorem sin_parts (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im ∧
    (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  rw [Complex.sin_eq]
  constructor <;> simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

theorem cos_parts (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im ∧
    (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [Complex.cos_eq]
  constructor <;> simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

theorem memC_ccosSinPi {c : Cfg} {z : ℂ} {a co si : CBall} (hz : memC c.P z a)
    (h : ccosSinPi c a = some (co, si)) :
    memC c.P (Complex.cos (π * z)) co ∧ memC c.P (Complex.sin (π * z)) si := by
  unfold ccosSinPi at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨C, S⟩, hcs, ⟨ch, sh⟩, hhs, rfl, rfl⟩ := h
  have hx := mem_cosSinTurn (mem_shr 1 hz.1) hcs
  have hy := mem_coshSinhPi hz.2 hhs
  have e : 2 * π * (z.re / 2 ^ 1) = π * z.re := by ring
  rw [e] at hx
  have hre : (π * z : ℂ).re = π * z.re := by simp
  have him : (π * z : ℂ).im = π * z.im := by simp
  obtain ⟨c1, c2⟩ := cos_parts (π * z)
  obtain ⟨s1, s2⟩ := sin_parts (π * z)
  rw [hre, him] at c1 c2 s1 s2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [c1]; exact mem_mul hx.1 hy.1
  · rw [c2]; exact mem_neg (mem_mul hx.2 hy.2)
  · rw [s1]; exact mem_mul hx.2 hy.1
  · rw [s2]; exact mem_mul hx.1 hy.2

theorem memC_piz {c : Cfg} {z : ℂ} {a : CBall} (hz : memC c.P z a) :
    memC c.P ((π : ℂ) * z) (CBall.mulR c.P (piB c.P) a) :=
  memC_mulR (mem_piB c.P) hz

theorem memC_cS {c : Cfg} {z : ℂ} {a w : CBall} (hz : memC c.P z a) (h : cS c a = some w) :
    z ≠ 0 ∧ memC c.P (C64.S z) w := by
  unfold cS at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨co, si⟩, hcs, hd⟩ := h
  obtain ⟨_, hsi⟩ := memC_ccosSinPi hz hcs
  obtain ⟨hpz, hw⟩ := cdiv_sound hsi (memC_piz hz) hd
  have hz0 : z ≠ 0 := by intro h0; apply hpz; rw [h0, mul_zero]
  refine ⟨hz0, ?_⟩
  simp only [C64.S, hz0, ↓reduceIte]; exact hw

theorem memC_cS1 {c : Cfg} {z : ℂ} {a w : CBall} (hz : memC c.P z a) (h : cS1 c a = some w) :
    z ≠ 0 ∧ memC c.P (C64.S1 z) w := by
  unfold cS1 at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨⟨co, si⟩, hcs, hd⟩ := h
  obtain ⟨hco, hsi⟩ := memC_ccosSinPi hz hcs
  have hnum := memC_sub (memC_mul (memC_piz hz) hco) hsi
  have hden := memC_mul (memC_piz hz) hz
  obtain ⟨hd0, hw⟩ := cdiv_sound hnum hden hd
  have hz0 : z ≠ 0 := by intro h0; apply hd0; rw [h0, mul_zero]
  refine ⟨hz0, ?_⟩
  rw [C64.S1_eq hz0]
  convert hw using 2
  ring

theorem memC_cSS1 {c : Cfg} {z : ℂ} {a : CBall} {w w1 : CBall} (hz : memC c.P z a) (h : cSS1 c a = some (w, w1)) :
    z ≠ 0 ∧ memC c.P (C64.S z) w ∧ memC c.P (C64.S1 z) w1 := by
  unfold cSS1 at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨co, si⟩, hcs, s, hs, s1, hs1, rfl, rfl⟩ := h
  obtain ⟨hco, hsi⟩ := memC_ccosSinPi hz hcs
  obtain ⟨hpz, hw⟩ := cdiv_sound hsi (memC_piz hz) hs
  have hz0 : z ≠ 0 := by intro h0; apply hpz; rw [h0, mul_zero]
  refine ⟨hz0, ?_, ?_⟩
  · simp only [C64.S, hz0, ↓reduceIte]; exact hw
  · have hnum := CBall.memC_sub (CBall.memC_mul (memC_piz hz) hco) hsi
    have hden := CBall.memC_mul (memC_piz hz) hz
    obtain ⟨_, hw1⟩ := cdiv_sound hnum hden hs1
    rw [C64.S1_eq hz0]
    convert hw1 using 2
    ring

end C64Num
