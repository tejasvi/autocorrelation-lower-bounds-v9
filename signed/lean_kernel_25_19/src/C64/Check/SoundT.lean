import C64.Check.SoundBase
import C64.Calc

/-!
# Soundness of the checker, part 2: bounds in `t` (`cells`, `tbound`)

`f(t) = Σ_j Re(c_j K_t(ζ_j))`.  On a cell `[t_c - δ, t_c + δ]` (`δ = 2^{-e} ≤ 1/32`) Taylor's theorem gives
`f(t) ≤ f(t_c) + δ |f'(t_c)| + δ² M₂ / 2` with `M₂ = Σ_j |c_j K_{t_c}(ζ_j)| |2πζ_j|² e^{2π |Im ζ_j| / 32}`, since
`|K_t(ζ)| = |K_{t_c}(ζ)| |K_{t - t_c}(ζ)|` and `|K_s(ζ)| ≤ e^{2π |s| |Im ζ|}`.
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-- `f(t) = Σ_j Re(c_j K_t(ζ_j))`. -/
noncomputable def fsum (cz : List (ℂ × ℂ)) (t : ℝ) : ℝ := (cz.map fun p => (p.1 * C64.Kt t p.2).re).sum

/-- `w(ζ) = -2πiζ`, so that `d/dt K_t(ζ) = w(ζ) K_t(ζ)`. -/
noncomputable def wOf (ζ : ℂ) : ℂ := -2 * π * Complex.I * ζ

noncomputable def f1sum (cz : List (ℂ × ℂ)) (t : ℝ) : ℝ :=
  (cz.map fun p => (p.1 * wOf p.2 * C64.Kt t p.2).re).sum

noncomputable def f2sum (cz : List (ℂ × ℂ)) (t : ℝ) : ℝ :=
  (cz.map fun p => (p.1 * wOf p.2 ^ 2 * C64.Kt t p.2).re).sum

/-! ### `K_t` as a function of `t` -/

theorem Kt_zero (ζ : ℂ) : C64.Kt 0 ζ = 1 := by simp [C64.Kt]

theorem norm_Kt_le_abs (s : ℝ) (ζ : ℂ) : ‖C64.Kt s ζ‖ ≤ Real.exp (2 * π * |s| * |ζ.im|) := by
  rw [C64.norm_Kt]
  apply Real.exp_le_exp.2
  have h1 : s * ζ.im ≤ |s| * |ζ.im| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [Real.pi_pos]

theorem Kt_eq_exp (s : ℝ) (ζ : ℂ) : C64.Kt s ζ = Complex.exp (wOf ζ * s) := by
  unfold C64.Kt wOf; congr 1; ring

/-- `d/dt Re(c K_t(ζ)) = Re(c w(ζ) K_t(ζ))`. -/
theorem hasDerivAt_term (c ζ : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (c * C64.Kt s ζ).re) (c * wOf ζ * C64.Kt t ζ).re t := by
  have he : HasDerivAt (fun z : ℂ => c * Complex.exp (wOf ζ * z)) (c * (Complex.exp (wOf ζ * t) * wOf ζ)) (t : ℂ) :=
    (((hasDerivAt_id (t : ℂ)).const_mul (wOf ζ)).cexp.const_mul c).congr_deriv (by simp)
  have := he.real_of_complex
  simp only [← Kt_eq_exp] at this
  convert this using 2
  ring

theorem hasDerivAt_fsum (cz : List (ℂ × ℂ)) (t : ℝ) : HasDerivAt (fsum cz) (f1sum cz t) t := by
  induction cz with
  | nil => simp only [fsum, f1sum, List.map_nil, List.sum_nil]; exact hasDerivAt_const t 0
  | cons p cz ih =>
    simp only [fsum, f1sum, List.map_cons, List.sum_cons] at ih ⊢
    exact (hasDerivAt_term p.1 p.2 t).add ih

theorem hasDerivAt_f1sum (cz : List (ℂ × ℂ)) (t : ℝ) : HasDerivAt (f1sum cz) (f2sum cz t) t := by
  induction cz with
  | nil => simp only [f1sum, f2sum, List.map_nil, List.sum_nil]; exact hasDerivAt_const t 0
  | cons p cz ih =>
    simp only [f1sum, f2sum, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := hasDerivAt_term (p.1 * wOf p.2) p.2 t
    rw [show p.1 * wOf p.2 * wOf p.2 * C64.Kt t p.2 = p.1 * wOf p.2 ^ 2 * C64.Kt t p.2 by ring] at h1
    exact h1.add ih

/-! ### Term states -/

/-- The semantics of a term state at the cell `(t_c, e)`. -/
structure TermOK (P : ℕ) (tc : ℝ) (e : ℕ) (c ζ : ℂ) (T : TermS) : Prop where
  W : memC P (c * C64.Kt tc ζ) T.W
  w : memC P (wOf ζ) T.w
  st : ∀ i y, T.st[i]? = some y → memC P (C64.Kt (1 / 2 ^ (e + 1 + i)) ζ) y.1 ∧
        memC P (C64.Kt (-(1 / 2 ^ (e + 1 + i))) ζ) y.2
  m2 : ‖wOf ζ‖ ^ 2 * Real.exp (2 * π * |ζ.im| / 32) ≤ (T.m2 : ℝ) / 2 ^ P

/-- The semantics of a point table. -/
structure PtOK (P : ℕ) (D : ℕ) (ζ : ℂ) (T : PtT) : Prop where
  len : T.st.length = D
  st : ∀ i y, T.st[i]? = some y → memC P (C64.Kt (1 / 2 ^ (2 + i)) ζ) y.1 ∧
        memC P (C64.Kt (-(1 / 2 ^ (2 + i))) ζ) y.2
  w : memC P (wOf ζ) T.w
  mz : ‖wOf ζ‖ ^ 2 * Real.exp (2 * π * |ζ.im| / 32) ≤ (T.mz : ℝ) / 2 ^ P

theorem termOf_ok {D : ℕ} {c ζ : ℂ} {cf : CBall} {T : PtT} (hT : PtOK P D ζ T) (hc : memC P c cf) :
    TermOK P 0 1 c ζ (termOf cf T) := by
  refine ⟨?_, hT.w, ?_, hT.mz⟩
  · simp only [termOf, Kt_zero, mul_one]; exact hc
  · intro i y hy
    have := hT.st i y hy
    rw [show 1 + 1 + i = 2 + i by ring]; exact this

theorem termOf_len {cf : CBall} {T : PtT} : (termOf cf T).st.length = T.st.length := rfl

theorem stepT_ok {tc : ℝ} {e : ℕ} {c ζ : ℂ} {T : TermS} (hT : TermOK P tc e c ζ T) (hne : T.st ≠ []) (down : Bool) :
    TermOK P (if down then tc - 1 / 2 ^ (e + 1) else tc + 1 / 2 ^ (e + 1)) (e + 1) c ζ (stepT P down T) := by
  obtain ⟨W, w, st, m2⟩ := T
  cases st with
  | nil => exact absurd rfl hne
  | cons x rest =>
    obtain ⟨kp, km⟩ := x
    have h0 := hT.st 0 (kp, km) rfl
    simp only [add_zero] at h0
    refine ⟨?_, hT.w, ?_, hT.m2⟩
    · simp only [stepT]
      have hW := hT.W
      cases down
      · simp only [Bool.false_eq_true, if_false]
        rw [C64.Kt_add, ← mul_assoc]
        exact C64Num.CBall.memC_mul hW h0.1
      · simp only [if_true]
        rw [sub_eq_add_neg, C64.Kt_add, ← mul_assoc]
        exact C64Num.CBall.memC_mul hW h0.2
    · intro i y hy
      have := hT.st (i + 1) y (by simpa [stepT] using hy)
      rw [show e + 1 + 1 + i = e + 1 + (i + 1) by ring]; exact this

theorem stepT_len {T : TermS} (hne : T.st ≠ []) (down : Bool) : (stepT P down T).st.length + 1 = T.st.length := by
  obtain ⟨W, w, st, m2⟩ := T
  cases st with
  | nil => exact absurd rfl hne
  | cons x rest => obtain ⟨kp, km⟩ := x; simp [stepT]

/-! ### The cell bound -/

theorem sumTerms_ok {tc : ℝ} {e : ℕ} : ∀ (czs : List (ℂ × ℂ)) (ts : List TermS),
    List.Forall₂ (fun cz T => TermOK P tc e cz.1 cz.2 T) czs ts →
    mem P (fsum czs tc) (sumTerms P ts).1 ∧ mem P (f1sum czs tc) (sumTerms P ts).2.1 ∧
      (czs.map fun p => ‖p.1 * C64.Kt tc p.2‖ * (‖wOf p.2‖ ^ 2 * Real.exp (2 * π * |p.2.im| / 32))).sum ≤
        ((sumTerms P ts).2.2 : ℝ) / 2 ^ P
  | [], [], _ => by
    refine ⟨?_, ?_, ?_⟩ <;> simp [sumTerms, fsum, f1sum, mem]
  | cz :: czs, T :: ts, h => by
    obtain ⟨hT, hrest⟩ := List.forall₂_cons.1 h
    obtain ⟨i1, i2, i3⟩ := sumTerms_ok czs ts hrest
    simp only [sumTerms, fsum, f1sum, List.map_cons, List.sum_cons] at i1 i2 i3 ⊢
    refine ⟨mem_add hT.W.1 i1, ?_, ?_⟩
    · have := (C64Num.CBall.memC_mul hT.W hT.w).1
      rw [show cz.1 * wOf cz.2 * C64.Kt tc cz.2 = cz.1 * C64.Kt tc cz.2 * wOf cz.2 by ring]
      exact mem_add this i2
    · have hP := two_pow_pos' P
      have hn : ‖cz.1 * C64.Kt tc cz.2‖ ≤ ((T.W.re.absHi + T.W.im.absHi : ℕ) : ℝ) / 2 ^ P := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        push_cast; rw [add_div]
        exact add_le_add (abs_le_absHi hT.W.1) (abs_le_absHi hT.W.2)
      have := mulU_le (norm_nonneg _) (by positivity) hn hT.m2
      push_cast
      rw [add_div]
      exact add_le_add this i3
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem cellOK_ok {target : ℤ} {tc : ℝ} {e : ℕ} {czs : List (ℂ × ℂ)} {ts : List TermS}
    (h : cellOK P ts e target = true) (hts : List.Forall₂ (fun cz T => TermOK P tc e cz.1 cz.2 T) czs ts) :
    ∀ t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), fsum czs t < (target : ℝ) / 2 ^ P := by
  unfold cellOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨he5, hlt⟩ := h
  obtain ⟨i1, i2, i3⟩ := sumTerms_ok czs ts hts
  set f := (sumTerms P ts).1
  set f1 := (sumTerms P ts).2.1
  set m := (sumTerms P ts).2.2
  have hP := two_pow_pos' P
  have hδ : (1 : ℝ) / 2 ^ e ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (32 : ℝ) ≤ 2 ^ e := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he5
    linarith
  set M := (czs.map fun p => ‖p.1 * C64.Kt tc p.2‖ * (‖wOf p.2‖ ^ 2 * Real.exp (2 * π * |p.2.im| / 32))).sum
  have hM : ∀ x ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), |f2sum czs x| ≤ M := by
    intro x hx
    have hxd : |x - tc| ≤ 1 / 32 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    clear i1 i2 i3 hts
    unfold f2sum
    simp only [M]
    induction czs with
    | nil => simp
    | cons p czs ih =>
      simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans (add_le_add ?_ ih)
      refine (Complex.abs_re_le_norm _).trans ?_
      have hk : C64.Kt x p.2 = C64.Kt tc p.2 * C64.Kt (x - tc) p.2 := by
        rw [← C64.Kt_add]; congr 1; ring
      have hb : ‖C64.Kt (x - tc) p.2‖ ≤ Real.exp (2 * π * |p.2.im| / 32) := by
        refine (norm_Kt_le_abs _ _).trans (Real.exp_le_exp.2 ?_)
        have := mul_le_mul_of_nonneg_right hxd (abs_nonneg p.2.im)
        nlinarith [Real.pi_pos, abs_nonneg p.2.im]
      rw [hk, show p.1 * wOf p.2 ^ 2 * (C64.Kt tc p.2 * C64.Kt (x - tc) p.2) =
        (p.1 * C64.Kt tc p.2) * C64.Kt (x - tc) p.2 * wOf p.2 ^ 2 by ring, norm_mul, norm_mul, norm_pow]
      have h0 : 0 ≤ ‖p.1 * C64.Kt tc p.2‖ := norm_nonneg _
      calc ‖p.1 * C64.Kt tc p.2‖ * ‖C64.Kt (x - tc) p.2‖ * ‖wOf p.2‖ ^ 2
          ≤ ‖p.1 * C64.Kt tc p.2‖ * Real.exp (2 * π * |p.2.im| / 32) * ‖wOf p.2‖ ^ 2 := by gcongr
        _ = ‖p.1 * C64.Kt tc p.2‖ * (‖wOf p.2‖ ^ 2 * Real.exp (2 * π * |p.2.im| / 32)) := by ring
  intro t ht
  have hT := C64.taylor2_upper (hasDerivAt_fsum czs) (hasDerivAt_f1sum czs) (by positivity) hM t ht
  have hf := (mem_iff_lo_hi.1 i1).2
  have hf1 := abs_le_absHi i2
  have h1 : |f1sum czs tc| * (1 / 2 ^ e) ≤ (Ball.cdiv f1.absHi (2 ^ e) : ℝ) / 2 ^ P := by
    have := cdiv_le (P := P) (d := 2 ^ e) (by positivity) hf1
    push_cast at this
    calc |f1sum czs tc| * (1 / 2 ^ e) = |f1sum czs tc| / 2 ^ e := by ring
      _ ≤ _ := this
  have h2 : M * (1 / 2 ^ e) ^ 2 / 2 ≤ (Ball.cdiv m (2 ^ (2 * e + 1)) : ℝ) / 2 ^ P := by
    have := cdiv_le (P := P) (d := 2 ^ (2 * e + 1)) (by positivity) i3
    push_cast at this
    calc M * (1 / 2 ^ e) ^ 2 / 2 = M / 2 ^ (2 * e + 1) := by
          rw [show (2 : ℝ) ^ (2 * e + 1) = 2 ^ e * 2 ^ e * 2 by rw [pow_succ, two_mul, pow_add]]; field_simp
      _ ≤ _ := this
  have hlt' : ((f.hi + (Ball.cdiv f1.absHi (2 ^ e) : ℕ) + (Ball.cdiv m (2 ^ (2 * e + 1)) : ℕ) : ℤ) : ℝ) < target := by
    exact_mod_cast hlt
  push_cast at hlt'
  have : (f.hi : ℝ) / 2 ^ P + (Ball.cdiv f1.absHi (2 ^ e) : ℝ) / 2 ^ P + (Ball.cdiv m (2 ^ (2 * e + 1)) : ℝ) / 2 ^ P <
      (target : ℝ) / 2 ^ P := by
    rw [← add_div, ← add_div]; exact div_lt_div_of_pos_right hlt' hP
  linarith

/-! ### The cell tree -/

theorem cells_ok (target : ℤ) : ∀ (fuel skip e : ℕ) (ts : List TermS) (czs : List (ℂ × ℂ)) (tc : ℝ),
    cells P target fuel skip e ts = true →
    List.Forall₂ (fun cz T => TermOK P tc e cz.1 cz.2 T) czs ts →
    (∀ T ∈ ts, fuel ≤ T.st.length + 1) →
    ∀ t ∈ Set.Icc (tc - 1 / 2 ^ e) (tc + 1 / 2 ^ e), fsum czs t < (target : ℝ) / 2 ^ P
  | 0, _, _, _, _, _, h, _, _ => by simp [cells] at h
  | fuel + 1, skip, e, ts, czs, tc, h, hts, hlen => by
    unfold cells at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨_, hc⟩ | ⟨hd, hu⟩
    · exact cellOK_ok hc hts
    · -- both children; the fuel is positive, so every step list is nonempty
      cases fuel with
      | zero => simp [cells] at hd
      | succ f =>
        have hne : ∀ T ∈ ts, T.st ≠ [] := by
          intro T hT h0; have := hlen T hT; rw [h0] at this; simp at this
        have hchild : ∀ down : Bool, List.Forall₂ (fun cz T => TermOK P
            (if down then tc - 1 / 2 ^ (e + 1) else tc + 1 / 2 ^ (e + 1)) (e + 1) cz.1 cz.2 T) czs
            (ts.map (stepT P down)) := by
          intro down
          clear hd hu
          induction hts with
          | nil => exact List.Forall₂.nil
          | cons hab _ ih =>
            simp only [List.map_cons]
            refine List.Forall₂.cons (stepT_ok hab (hne _ (by simp)) down) ?_
            exact ih (fun T hT => hlen T (by simp [hT])) (fun T hT => hne T (by simp [hT]))
        have hlen' : ∀ down : Bool, ∀ T ∈ ts.map (stepT P down), f + 1 ≤ T.st.length + 1 := by
          intro down T hT
          obtain ⟨T0, hT0, rfl⟩ := List.mem_map.1 hT
          have h1 := stepT_len (P := P) (hne T0 hT0) down
          have := hlen T0 hT0; omega
        intro t ht
        rcases le_total t tc with htc | htc
        · have := cells_ok target (f + 1) (skip - 1) (e + 1) _ czs _ hd (hchild true) (hlen' true) t ⟨?_, ?_⟩
          · simpa using this
          · simp only [if_true]; rw [pow_succ]; linarith [ht.1, show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by
              field_simp]
          · simp only [if_true]; rw [pow_succ]; linarith [show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]
        · have := cells_ok target (f + 1) (skip - 1) (e + 1) _ czs _ hu (hchild false) (hlen' false) t ⟨?_, ?_⟩
          · simpa using this
          · simp only [Bool.false_eq_true, if_false]; rw [pow_succ]
            linarith [show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]
          · simp only [Bool.false_eq_true, if_false]; rw [pow_succ]
            linarith [ht.2, show (1 : ℝ) / 2 ^ e = 1 / (2 ^ e * 2) * 2 by field_simp]

theorem tbound_ok {D : ℕ} {target : ℤ} {ts : List TermS} {czs : List (ℂ × ℂ)}
    (h : tbound P D ts target = true) (hts : List.Forall₂ (fun cz T => TermOK P 0 1 cz.1 cz.2 T) czs ts)
    (hlen : ∀ T ∈ ts, T.st.length = D) :
    ∀ t ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), fsum czs t < (target : ℝ) / 2 ^ P := by
  intro t ht
  refine cells_ok target (D + 1) 4 1 ts czs 0 h hts (fun T hT => by rw [hlen T hT]) t ?_
  norm_num at ht ⊢; exact ht

end C64Chk

/-! ### Point tables -/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

theorem sqChain_len (P : ℕ) : ∀ (j : ℕ) (x : CBall × CBall) (acc : List (CBall × CBall)),
    (sqChain P j x acc).length = j + 1 + acc.length
  | 0, x, acc => by simp [sqChain]; ring
  | j + 1, x, acc => by rw [sqChain, sqChain_len P j]; simp; ring

theorem sqChain_zero (P : ℕ) (x : CBall × CBall) (acc : List (CBall × CBall)) : sqChain P 0 x acc = x :: acc := rfl

theorem sqChain_succ (P j : ℕ) (x : CBall × CBall) (acc : List (CBall × CBall)) :
    sqChain P (j + 1) x acc = sqChain P j (CBall.mul P x.1 x.1, CBall.mul P x.2 x.2) (x :: acc) := rfl

/-- The squaring chain: entry `i` (from the head) of `sqChain P j x acc` is `x^(2^(j-i))`. -/
theorem sqChain_ok {ζ : ℂ} (j : ℕ) : ∀ (h : ℝ) (x : CBall × CBall) (acc : List (CBall × CBall)),
    memC P (C64.Kt h ζ) x.1 → memC P (C64.Kt (-h) ζ) x.2 →
    (∀ i y, acc[i]? = some y → memC P (C64.Kt (h / 2 ^ (i + 1)) ζ) y.1 ∧
      memC P (C64.Kt (-(h / 2 ^ (i + 1))) ζ) y.2) →
    ∀ i y, (sqChain P j x acc)[i]? = some y →
      memC P (C64.Kt (h * 2 ^ j / 2 ^ i) ζ) y.1 ∧ memC P (C64.Kt (-(h * 2 ^ j / 2 ^ i)) ζ) y.2 := by
  induction j with
  | zero =>
    intro h x acc h1 h2 hacc i y hy
    rw [sqChain_zero] at hy
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      simp only [pow_zero, mul_one, div_one]; exact ⟨h1, h2⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hy
      have := hacc i y hy
      rw [pow_zero, mul_one]; exact this
  | succ j ih =>
    intro h x acc h1 h2 hacc i y hy
    rw [sqChain_succ] at hy
    have hsq1 : memC P (C64.Kt (2 * h) ζ) (CBall.mul P x.1 x.1) := by
      rw [two_mul, C64.Kt_add]; exact C64Num.CBall.memC_mul h1 h1
    have hsq2 : memC P (C64.Kt (-(2 * h)) ζ) (CBall.mul P x.2 x.2) := by
      rw [show -(2 * h) = -h + -h by ring, C64.Kt_add]; exact C64Num.CBall.memC_mul h2 h2
    have hacc' : ∀ i y, (x :: acc)[i]? = some y → memC P (C64.Kt (2 * h / 2 ^ (i + 1)) ζ) y.1 ∧
        memC P (C64.Kt (-(2 * h / 2 ^ (i + 1))) ζ) y.2 := by
      intro i y hy
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        rw [zero_add, pow_one, mul_div_cancel_left₀ _ two_ne_zero]; exact ⟨h1, h2⟩
      | succ i =>
        rw [List.getElem?_cons_succ] at hy
        have := hacc i y hy
        rw [show 2 * h / 2 ^ (i + 1 + 1) = h / 2 ^ (i + 1) by rw [pow_succ]; field_simp]
        exact this
    have := ih (2 * h) (CBall.mul P x.1 x.1, CBall.mul P x.2 x.2) (x :: acc) hsq1 hsq2 hacc' i y hy
    rw [show 2 * h * 2 ^ j = h * 2 ^ (j + 1) by rw [pow_succ]; ring] at this
    exact this

theorem ptT_ok {c : Cfg} {D : ℕ} {ζ : ℂ} {z : CBall} {T : PtT} (hz : memC c.P ζ z) (hD : 1 ≤ D)
    (hDP : D + 1 ≤ c.P) (h : ptT c D z = some T) : PtOK c.P D ζ T := by
  unfold ptT at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨kp, hkp, km, hkm, f0, hf0, rfl⟩ := h
  have hh := mem_dyB (P := c.P) 1 hDP
  push_cast at hh
  have h1 := memC_ckt hh hz hkp
  have h2 := memC_ckt (mem_neg hh) hz hkm
  have hP := two_pow_pos' c.P
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sqChain_len]; simp; omega
  · intro i y hy
    have := sqChain_ok (P := c.P) (ζ := ζ) (D - 1) (1 / 2 ^ (D + 1)) (kp, km) [] h1 h2 (by simp) i y hy
    have e : (1 : ℝ) / 2 ^ (D + 1) * 2 ^ (D - 1) / 2 ^ i = 1 / 2 ^ (2 + i) := by
      have hD' : D + 1 = (D - 1) + 2 := by omega
      rw [hD', pow_add, pow_add]; field_simp
    rw [e] at this; exact this
  · refine ⟨?_, ?_⟩
    · have := mem_mulInt 2 (mem_mul (mem_piB c.P) hz.2)
      simp only [wOf, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      convert this using 1; push_cast; ring
    · have := mem_neg (mem_mulInt 2 (mem_mul (mem_piB c.P) hz.1))
      simp only [wOf, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      convert this using 1; push_cast; ring
  · -- ‖w‖² e^{2π|Im ζ|/32} ≤ mz
    have hw : ‖wOf ζ‖ ^ 2 ≤ 4 * (mulU c.P (piSqHi c.P) (mulU c.P (normHi z) (normHi z)) : ℝ) / 2 ^ c.P := by
      have hn := norm_le_normHi hz
      have hpi := pi_le_piHi (P := c.P)
      have hpisq : π ^ 2 ≤ (piSqHi c.P : ℝ) / 2 ^ c.P := by
        unfold piSqHi
        have := cdiv_le (P := c.P) (x := π ^ 2 * 2 ^ c.P) (X := piHi c.P ^ 2) (d := 2 ^ c.P) (by positivity) ?_
        · rw [show π ^ 2 * 2 ^ c.P / ((2 ^ c.P : ℕ) : ℝ) = π ^ 2 by push_cast; field_simp] at this; exact this
        · push_cast
          calc π ^ 2 * 2 ^ c.P ≤ ((piHi c.P : ℝ) / 2 ^ c.P) ^ 2 * 2 ^ c.P := by gcongr
            _ = (piHi c.P : ℝ) ^ 2 / 2 ^ c.P := by field_simp
      have hn2 : ‖ζ‖ ^ 2 ≤ (mulU c.P (normHi z) (normHi z) : ℝ) / 2 ^ c.P := by
        rw [sq]; exact mulU_le (norm_nonneg _) (norm_nonneg _) hn hn
      have hm := mulU_le (sq_nonneg π) (sq_nonneg ‖ζ‖) hpisq hn2
      have : ‖wOf ζ‖ ^ 2 = 4 * (π ^ 2 * ‖ζ‖ ^ 2) := by
        unfold wOf
        rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        ring
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hm (by norm_num)
    have he : Real.exp (2 * π * |ζ.im| / 32) ≤ (f0 : ℝ) / 2 ^ c.P := by
      have hy : |ζ.im| / 16 ≤ (Ball.cdiv z.im.absHi 16 : ℝ) / 2 ^ c.P :=
        cdiv_le (by norm_num) (abs_le_absHi hz.2)
      have := exp_le_expPiHi hf0 hy
      rw [show 2 * π * |ζ.im| / 32 = π * (|ζ.im| / 16) by ring]; exact this
    have := mulU_le (x := ‖wOf ζ‖ ^ 2) (sq_nonneg _) (Real.exp_pos _).le (X := 4 * mulU c.P (piSqHi c.P) (mulU c.P (normHi z) (normHi z))) (by push_cast; exact hw) he
    push_cast at this ⊢
    exact this

end C64Chk
