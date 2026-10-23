import Autocorr.KSound.Step

/-!
# Soundness of the square-cut step of the kernel checker

`cutStep` (AutocorrK/Core.lean) reads a cut `(v0, d, v1, e, v2)` with the dual `y = M / 2^94 ≥ 0` and adds
`-y·coef` of every coefficient of the row
`v1² [m_d m_d] + 2 v1 v2 [m_d m_e] + v2² [m_e m_e] + 2 v0 v1 m_d + 2 v0 v2 m_e ≥ -v0²`
to the reduced costs (positive coefficients to `rn`, negative ones to `rp`) and `y·(-v0²)` to the row part (`an`).
At the true point the left side plus `v0²` is `(v0 + v1 m_d + v2 m_e)² ≥ 0` (`xval_canon`, `xval_m`), so the
validity quantity `vq` of the step is `-y (v0 + v1 m_d + v2 m_e)² ≤ 0` (`cutStep_spec`).
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

variable {sp : Spec} {P : KP}

/-! ## The product-column table -/

lemma canonOK_row (d : ℕ) : ∀ k, (Nat.rec (motive := fun _ => Bool) true
    (fun e ih2 => Nat.beq (canonT P d e) (sp.canon d e) && ih2) k : Bool) = true →
    ∀ e < k, canonT P d e = sp.canon d e := by
  intro k
  induction k with
  | zero => intro _ e he; omega
  | succ k ih =>
    intro h e he
    have h' : Nat.beq (canonT P d k) (sp.canon d k) = true ∧ (Nat.rec (motive := fun _ => Bool) true
        (fun e ih2 => Nat.beq (canonT P d e) (sp.canon d e) && ih2) k : Bool) = true := by
      simpa only [Bool.and_eq_true] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp he with h'' | h''
    · exact ih h'.2 e h''
    · subst h''; exact Nat.beq_eq.mp h'.1

lemma canonOK_all : ∀ k, (Nat.rec (motive := fun _ => Bool) true
    (fun d ih => Nat.rec (motive := fun _ => Bool) true
      (fun e ih2 => Nat.beq (canonT P d e) (sp.canon d e) && ih2) sp.nB && ih) k : Bool) = true →
    ∀ d < k, ∀ e < sp.nB, canonT P d e = sp.canon d e := by
  intro k
  induction k with
  | zero => intro _ d hd; omega
  | succ k ih =>
    intro h d hd e he
    have h' : (Nat.rec (motive := fun _ => Bool) true
          (fun e ih2 => Nat.beq (canonT P k e) (sp.canon k e) && ih2) sp.nB : Bool) = true ∧
        (Nat.rec (motive := fun _ => Bool) true
          (fun d ih => Nat.rec (motive := fun _ => Bool) true
            (fun e ih2 => Nat.beq (canonT P d e) (sp.canon d e) && ih2) sp.nB && ih) k : Bool) = true := by
      simpa only [Bool.and_eq_true] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with h'' | h''
    · exact ih h'.2 d h'' e he
    · subst h''; exact canonOK_row d sp.nB h'.1 e he

lemma canonT_eq (hkp : KPFacts sp P) {d e : ℕ} (hd : d < sp.nB) (he : e < sp.nB) :
    canonT P d e = sp.canon d e :=
  canonOK_all sp.nB hkp.canon d hd e he

lemma nB_le_oT : sp.nB ≤ sp.oT := by rw [oT_eq]; omega

/-! ## Arithmetic of one cut -/

lemma sel_cast (b : Bool) (u v : ℕ) : ((sel b u v : ℕ) : ℝ) = if b = true then (u : ℝ) else v := by
  cases b <;> rfl

/-- The sign `±1` of a sign bit. -/
noncomputable def sgn (s : ℕ) : ℝ := if s = 1 then -1 else 1

lemma sgn_sq {s : ℕ} : sgn s * sgn s = 1 := by unfold sgn; split_ifs <;> norm_num

lemma sgn_pair {s s' : ℕ} (hs : s < 2) (hs' : s' < 2) :
    (if Nat.beq s s' = true then (1 : ℝ) else -1) = sgn s * sgn s' := by
  interval_cases s <;> interval_cases s' <;> simp [sgn]

lemma blt_true' {a b : ℕ} (h : a < b) : Nat.blt a b = true := Nat.blt_eq.mpr h
lemma blt_false' {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hb) h

/-- The validity quantity of a cut is `-(M/2^94)·(v0 + v1 m_d + v2 m_e)²`. -/
lemma cut_vq_le {M a0 a1 a2 md me e0 e1 e2 : ℝ} (hM : 0 ≤ M) (h0 : e0 * e0 = 1) (h1 : e1 * e1 = 1)
    (h2 : e2 * e2 = 1) :
    -(M * (a0 * a0) * 2 ^ 30) / 2 ^ 124 +
      -(M * (a1 * a1 * (md * md) + a2 * a2 * (me * me) + e1 * e2 * (2 * (a1 * a2)) * (md * me) +
        e0 * e1 * (2 * (a0 * a1)) * md + e0 * e2 * (2 * (a0 * a2)) * me)) / 2 ^ 94 ≤ 0 := by
  have key : a0 * a0 + (a1 * a1 * (md * md) + a2 * a2 * (me * me) + e1 * e2 * (2 * (a1 * a2)) * (md * me) +
      e0 * e1 * (2 * (a0 * a1)) * md + e0 * e2 * (2 * (a0 * a2)) * me) =
      (e0 * a0 + e1 * a1 * md + e2 * a2 * me) ^ 2 := by
    have q : (e0 * a0 + e1 * a1 * md + e2 * a2 * me) ^ 2 =
        (e0 * e0) * (a0 * a0) + (e1 * e1) * (a1 * a1 * (md * md)) + (e2 * e2) * (a2 * a2 * (me * me)) +
        e1 * e2 * (2 * (a1 * a2)) * (md * me) + e0 * e1 * (2 * (a0 * a1)) * md + e0 * e2 * (2 * (a0 * a2)) * me := by
      ring
    rw [q, h0, h1, h2]; ring
  have hsq := sq_nonneg (e0 * a0 + e1 * a1 * md + e2 * a2 * me)
  have h94 : (0 : ℝ) < 2 ^ 94 := by positivity
  have e1' : -(M * (a0 * a0) * 2 ^ 30) / 2 ^ 124 = -(M * (a0 * a0)) / 2 ^ 94 := by
    rw [show (2 : ℝ) ^ 124 = 2 ^ 30 * 2 ^ 94 by norm_num]
    field_simp
  rw [e1', ← add_div, div_le_iff₀ h94, zero_mul]
  nlinarith [mul_nonneg hM hsq, key]

/-! ## The cut step -/

/-- What `cutStep` does, when it accepts. -/
theorem cutStep_spec (hkp : KPFacts sp P) (data : ℕ) (k : K) (rp rn tp tn ap an : ℕ)
    (h : cutStep P data k rp rn tp tn ap an = true) :
    ∃ (Lp Ln : List (ℕ × ℕ)) (dan : ℕ),
      k (Nat.shiftRight data 174) (rp + packL Lp) (rn + packL Ln) (tp + 0) (tn + 0) (ap + 0) (an + dan) = true ∧
      (∀ e ∈ Lp ++ Ln, e.1 < sp.oT ∧ e.2 ≤ 2 ^ 108) ∧ Lp.length + Ln.length ≤ 70 ∧
      (∀ p t, vq sp p t Lp Ln 0 0 0 dan ≤ 0) := by
  unfold cutStep at h
  simp only [] at h
  generalize hd : Nat.mod (Nat.shiftRight data 15) 128 = d at h
  generalize he : Nat.mod (Nat.shiftRight data 22) 128 = e at h
  generalize hs0 : Nat.mod (Nat.shiftRight data 29) 2 = s0 at h
  generalize ha0 : Nat.mod (Nat.shiftRight data 30) 2097152 = a0 at h
  generalize hs1 : Nat.mod (Nat.shiftRight data 51) 2 = s1 at h
  generalize ha1 : Nat.mod (Nat.shiftRight data 52) 2097152 = a1 at h
  generalize hs2 : Nat.mod (Nat.shiftRight data 73) 2 = s2 at h
  generalize ha2 : Nat.mod (Nat.shiftRight data 74) 2097152 = a2 at h
  generalize hM : Nat.mod (Nat.shiftRight data 95) 18446744073709551616 = M at h
  have bs0 : s0 < 2 := by rw [← hs0, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have bs1 : s1 < 2 := by rw [← hs1, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have bs2 : s2 < 2 := by rw [← hs2, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have ba0 : a0 < 2 ^ 21 := by rw [← ha0, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have ba1 : a1 < 2 ^ 21 := by rw [← ha1, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have ba2 : a2 < 2 ^ 21 := by rw [← ha2, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  have bM : M < 2 ^ 64 := by rw [← hM, raw_mod]; exact Nat.mod_lt _ (by norm_num)
  by_cases hdB : d < P.nB
  swap
  · rw [blt_false' hdB, sel_false] at h
    exact absurd h (by simp)
  rw [blt_true' hdB, sel_true] at h
  by_cases heB : e < P.nB
  swap
  · rw [blt_false' heB, sel_false] at h
    exact absurd h (by simp)
  rw [blt_true' heB, sel_true] at h
  have hd' : d < sp.nB := hkp.nB ▸ hdB
  have he' : e < sp.nB := hkp.nB ▸ heB
  rw [canonT_eq hkp hd' he', canonT_eq hkp hd' hd', canonT_eq hkp he' he'] at h
  generalize hb12 : Nat.beq s1 s2 = b12 at h
  generalize hb01 : Nat.beq s0 s1 = b01 at h
  generalize hb02 : Nat.beq s0 s2 = b02 at h
  generalize htde : Nat.mul 2 (Nat.mul M (Nat.mul a1 a2)) = tde at h
  generalize htmd : Nat.mul 2 (Nat.mul M (Nat.mul a0 a1)) = tmd at h
  generalize htme : Nat.mul 2 (Nat.mul M (Nat.mul a0 a2)) = tme at h
  refine ⟨[(sp.canon d e, sel b12 0 tde), (d, sel b01 0 tmd), (e, sel b02 0 tme)],
    [(sp.canon d d, M * (a1 * a1)), (sp.canon e e, M * (a2 * a2)), (sp.canon d e, sel b12 tde 0),
      (d, sel b01 tmd 0), (e, sel b02 tme 0)],
    M * (a0 * a0) * 2 ^ 30, ?_, ?_, ?_, ?_⟩
  · convert h using 2
    · simp only [packL_cons, packL_nil, atc, raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq, add_zero]
      try ring
    · simp only [packL_cons, packL_nil, atc, raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq, add_zero]
      try ring
    · simp only [raw_add, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq]
  · -- index and size bounds
    have hcde := canon_lt hkp.wf hd' he'
    have hcdd := canon_lt hkp.wf hd' hd'
    have hcee := canon_lt hkp.wf he' he'
    have hdT : d < sp.oT := lt_of_lt_of_le hd' nB_le_oT
    have heT : e < sp.oT := lt_of_lt_of_le he' nB_le_oT
    have b2 : ∀ x y : ℕ, x < 2 ^ 21 → y < 2 ^ 21 → 2 * (M * (x * y)) ≤ 2 ^ 108 := by
      intro x y hx hy
      calc 2 * (M * (x * y)) ≤ 2 * (2 ^ 64 * (2 ^ 21 * 2 ^ 21)) := by gcongr
        _ ≤ 2 ^ 108 := by norm_num
    have bde : tde ≤ 2 ^ 108 := by rw [← htde, raw_mul, raw_mul, raw_mul]; exact b2 _ _ ba1 ba2
    have bmd : tmd ≤ 2 ^ 108 := by rw [← htmd, raw_mul, raw_mul, raw_mul]; exact b2 _ _ ba0 ba1
    have bme : tme ≤ 2 ^ 108 := by rw [← htme, raw_mul, raw_mul, raw_mul]; exact b2 _ _ ba0 ba2
    have bdd : M * (a1 * a1) ≤ 2 ^ 108 := by
      calc M * (a1 * a1) ≤ 2 ^ 64 * (2 ^ 21 * 2 ^ 21) := by gcongr
        _ ≤ 2 ^ 108 := by norm_num
    have bee : M * (a2 * a2) ≤ 2 ^ 108 := by
      calc M * (a2 * a2) ≤ 2 ^ 64 * (2 ^ 21 * 2 ^ 21) := by gcongr
        _ ≤ 2 ^ 108 := by norm_num
    have hs : ∀ (b : Bool) (v : ℕ), v ≤ 2 ^ 108 → sel b 0 v ≤ 2 ^ 108 ∧ sel b v 0 ≤ 2 ^ 108 := by
      intro b v hv
      cases b
      · exact ⟨hv, Nat.zero_le _⟩
      · exact ⟨Nat.zero_le _, hv⟩
    intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hcde, (hs _ _ bde).1⟩
    · exact ⟨hdT, (hs _ _ bmd).1⟩
    · exact ⟨heT, (hs _ _ bme).1⟩
    · exact ⟨hcdd, bdd⟩
    · exact ⟨hcee, bee⟩
    · exact ⟨hcde, (hs _ _ bde).2⟩
    · exact ⟨hdT, (hs _ _ bmd).2⟩
    · exact ⟨heT, (hs _ _ bme).2⟩
  · simp
  · intro p t
    have hx1 := xval_canon (p := p) (t := t) hkp.wf hd' he'
    have hx2 := xval_canon (p := p) (t := t) hkp.wf hd' hd'
    have hx3 := xval_canon (p := p) (t := t) hkp.wf he' he'
    have hx4 := xval_m (p := p) (t := t) hd'
    have hx5 := xval_m (p := p) (t := t) he'
    have p12 := sgn_pair bs1 bs2
    have p01 := sgn_pair bs0 bs1
    have p02 := sgn_pair bs0 bs2
    rw [hb12] at p12
    rw [hb01] at p01
    rw [hb02] at p02
    set md := mass sp p d
    set me := mass sp p e
    -- the dot products, with the sign of each mixed coefficient
    have hdiff : ∀ (b : Bool) (v : ℕ) (x : ℝ),
        ((sel b 0 v : ℕ) : ℝ) * x - ((sel b v 0 : ℕ) : ℝ) * x = -((if b = true then (1 : ℝ) else -1) * v * x) := by
      intro b v x; cases b <;> simp [sel]
    have key : dotL [(sp.canon d e, sel b12 0 tde), (d, sel b01 0 tmd), (e, sel b02 0 tme)] (xval sp p t) -
        dotL [(sp.canon d d, M * (a1 * a1)), (sp.canon e e, M * (a2 * a2)), (sp.canon d e, sel b12 tde 0),
          (d, sel b01 tmd 0), (e, sel b02 tme 0)] (xval sp p t) =
        -((M : ℝ) * (a1 * a1 * (md * md) + a2 * a2 * (me * me) +
          (if b12 = true then (1 : ℝ) else -1) * (2 * (a1 * a2)) * (md * me) +
          (if b01 = true then (1 : ℝ) else -1) * (2 * (a0 * a1)) * md +
          (if b02 = true then (1 : ℝ) else -1) * (2 * (a0 * a2)) * me)) := by
      simp only [dotL_cons, dotL_nil, add_zero, hx1, hx2, hx3, hx4, hx5]
      have d1 := hdiff b12 tde (md * me)
      have d2 := hdiff b01 tmd md
      have d3 := hdiff b02 tme me
      have c1 : (tde : ℝ) = 2 * ((M : ℝ) * ((a1 : ℝ) * a2)) := by rw [← htde]; push_cast [raw_mul]; ring
      have c2 : (tmd : ℝ) = 2 * ((M : ℝ) * ((a0 : ℝ) * a1)) := by rw [← htmd]; push_cast [raw_mul]; ring
      have c3 : (tme : ℝ) = 2 * ((M : ℝ) * ((a0 : ℝ) * a2)) := by rw [← htme]; push_cast [raw_mul]; ring
      rw [c1] at d1; rw [c2] at d2; rw [c3] at d3
      push_cast
      linear_combination d1 + d2 + d3
    unfold vq
    rw [key, p12, p01, p02]
    have hfin := cut_vq_le (M := (M : ℝ)) (a0 := (a0 : ℝ)) (a1 := (a1 : ℝ)) (a2 := (a2 : ℝ)) (md := md)
      (me := me) (by positivity) (sgn_sq (s := s0)) (sgn_sq (s := s1)) (sgn_sq (s := s2))
    push_cast
    simp only [sub_self, zero_div, zero_mul, add_zero, zero_sub]
    linarith [hfin]

end AutocorrK
