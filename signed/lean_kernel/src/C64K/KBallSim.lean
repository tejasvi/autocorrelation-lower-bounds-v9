import Mathlib
import C64Core.Ival
import C64K.KBall

/-!
# Simulation lemmas: `KIval.KBall` computes exactly what `Ival.Ball` computes

`KBall.toBall ⟨s, m, r⟩ = ⟨(-1)^s m, r⟩`.  For every operation `op` of `Ival.Ball` the lemma `toBall_op` states
`toBall (KBall.op ..) = Ival.Ball.op (toBall ..)` (with `Prod.map toBall toBall` and `Option.map toBall` for pairs
and partial operations), so that a soundness proof about the `Ival` checker transfers to the kernel layer by
rewriting.
-/

namespace KIval

namespace KBall

/-- The signed integer `(-1)^s m`. -/
def sval (s : Bool) (m : Nat) : Int := cond s (-(m : Int)) m

/-- The `Ival.Ball` that a `KBall` stands for. -/
def toBall (a : KBall) : Ival.Ball := ⟨sval a.s a.m, a.r⟩

@[simp] lemma toBall_m (a : KBall) : (toBall a).m = sval a.s a.m := rfl
@[simp] lemma toBall_r (a : KBall) : (toBall a).r = a.r := rfl

lemma ball_ext {a b : Ival.Ball} (hm : a.m = b.m) (hr : a.r = b.r) : a = b := by
  cases a; cases b; simp_all

@[simp] lemma sval_false (m : Nat) : sval false m = m := rfl
@[simp] lemma sval_true (m : Nat) : sval true m = -(m : Int) := rfl

@[simp] lemma natAbs_sval (s : Bool) (m : Nat) : (sval s m).natAbs = m := by
  cases s <;> simp

/-! ## The primitives as the usual operations -/

@[simp] lemma nadd (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] lemma nsub (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] lemma nmul (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] lemma ndiv (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] lemma nmod (a b : Nat) : Nat.mod a b = a % b := rfl
@[simp] lemma npow (a b : Nat) : Nat.pow a b = a ^ b := rfl

@[simp] lemma nble (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.ble_eq])

@[simp] lemma nbeq (a b : Nat) : Nat.beq a b = decide (a = b) :=
  Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])

@[simp] lemma bx_eq (a b : Bool) : bx a b = (a ^^ b) := by cases a <;> cases b <;> rfl

@[simp] lemma blt_eq (a b : Nat) : blt a b = decide (a < b) := by
  unfold blt
  rw [nble, nadd]
  exact decide_eq_decide.2 (by omega)

@[simp] lemma cdiv_eq (n d : Nat) : cdiv n d = Ival.Ball.cdiv n d := rfl

/-! ## Rounding -/

lemma sval_xor (s₁ s₂ : Bool) (a b : Nat) : sval s₁ a * sval s₂ b = sval (s₁ ^^ s₂) (a * b) := by
  cases s₁ <;> cases s₂ <;> simp [sval]

/-- `rndD` is `Ival.Ball.rndN` on the signed value. -/
lemma sval_rndD (s : Bool) (m d r : Nat) :
    sval (rndD s m d r).s (rndD s m d r).m = Ival.Ball.rndN (sval s m) d := by
  unfold rndD Ival.Ball.rndN
  simp only [nadd, nsub, ndiv, nble]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · cases s <;> by_cases h : m ≤ 0 / 2 <;> simp [sval, h]
  · cases s
    · simp only [Bool.cond_false, sval_false]
      rw [Int.natCast_div, Nat.cast_add]
    · by_cases hmh : m ≤ d / 2
      · have h1 : (0 : Int) ≤ -(m : Int) + ((d / 2 : Nat) : Int) := by omega
        have h2 : -(m : Int) + ((d / 2 : Nat) : Int) < (d : Int) := by
          have : d / 2 < d := Nat.div_lt_self hd (by norm_num)
          omega
        simp only [hmh, decide_true, Bool.cond_true, sval_false, sval_true]
        rw [Int.ediv_eq_zero_of_lt h1 h2]
        rfl
      · have hmh' : d / 2 < m := lt_of_not_ge hmh
        have hneg : -(m : Int) + ((d / 2 : Nat) : Int) = Int.negSucc (m - d / 2 - 1) := by
          rw [Int.negSucc_eq]
          push_cast [Nat.sub_sub, Nat.cast_sub (show d / 2 + 1 ≤ m by omega)]
          ring
        have hnum : m + d - (d / 2 + 1) = (m - d / 2 - 1) + d := by omega
        simp only [hmh, decide_false, Bool.cond_false, Bool.cond_true, sval_true]
        rw [hneg, Int.negSucc_ediv _ (by exact_mod_cast hd), hnum, Nat.add_div_right _ hd]
        push_cast
        rfl

lemma toBall_rndD (s : Bool) (m d r : Nat) : toBall (rndD s m d r) = ⟨Ival.Ball.rndN (sval s m) d, r⟩ := by
  refine ball_ext (sval_rndD s m d r) ?_
  unfold rndD
  cases s <;> simp
  split_ifs <;> rfl

lemma rnd2_eq_rndN (p : Int) (k : Nat) : Ival.Ball.rnd2 p k = Ival.Ball.rndN p (2 ^ k) := rfl

/-! ## Signed sums and the field operations -/

lemma sval_sadd (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) :
    sval (sadd s₁ a s₂ b r).s (sadd s₁ a s₂ b r).m = sval s₁ a + sval s₂ b := by
  unfold sadd
  by_cases h : b ≤ a <;> cases s₁ <;> cases s₂ <;> simp [h, sval] <;> omega

@[simp] lemma sadd_r (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) : (sadd s₁ a s₂ b r).r = r := by
  unfold sadd
  by_cases h : b ≤ a <;> cases s₁ <;> cases s₂ <;> simp [h]

lemma toBall_sadd (s₁ : Bool) (a : Nat) (s₂ : Bool) (b r : Nat) :
    toBall (sadd s₁ a s₂ b r) = ⟨sval s₁ a + sval s₂ b, r⟩ :=
  ball_ext (sval_sadd s₁ a s₂ b r) (sadd_r s₁ a s₂ b r)

lemma sval_not (s : Bool) (m : Nat) : sval (cond s false true) m = -sval s m := by cases s <;> simp

@[simp] lemma sval_bnot (s : Bool) (m : Nat) : sval (!s) m = -sval s m := by cases s <;> simp

theorem toBall_ofInt (P : Nat) (s : Bool) (n : Nat) : toBall (ofInt P s n) = Ival.Ball.ofInt P (sval s n) := by
  refine ball_ext ?_ rfl
  cases s <;> simp [ofInt, Ival.Ball.ofInt, sval]

theorem toBall_ofRat (P : Nat) (s : Bool) (num den : Nat) :
    toBall (ofRat P s num den) = Ival.Ball.ofRat P (sval s num) den := by
  rw [ofRat, toBall_rndD]
  refine ball_ext ?_ rfl
  show Ival.Ball.rndN (sval s (num * 2 ^ P)) den = Ival.Ball.rndN (sval s num * ((2 ^ P : Nat) : Int)) den
  congr 1
  cases s <;> simp [sval]

theorem toBall_add (a b : KBall) : toBall (add a b) = Ival.Ball.add (toBall a) (toBall b) := by
  rw [add, toBall_sadd]
  rfl

theorem toBall_neg (a : KBall) : toBall (neg a) = Ival.Ball.neg (toBall a) := by
  refine ball_ext ?_ rfl
  simp [neg, Ival.Ball.neg]

theorem toBall_sub (a b : KBall) : toBall (sub a b) = Ival.Ball.sub (toBall a) (toBall b) := by
  rw [sub, toBall_sadd, sval_not]
  refine ball_ext ?_ rfl
  simp [Ival.Ball.sub, sub_eq_add_neg]

theorem toBall_mul (P : Nat) (a b : KBall) : toBall (mul P a b) = Ival.Ball.mul P (toBall a) (toBall b) := by
  rw [mul, toBall_rndD]
  refine ball_ext ?_ ?_
  · show Ival.Ball.rndN (sval (bx a.s b.s) (Nat.mul a.m b.m)) (Nat.pow 2 P) =
      Ival.Ball.rnd2 (sval a.s a.m * sval b.s b.m) P
    rw [rnd2_eq_rndN, sval_xor, bx_eq, nmul, npow]
  · simp [Ival.Ball.mul]

theorem toBall_mulInt (s : Bool) (n : Nat) (a : KBall) :
    toBall (mulInt s n a) = Ival.Ball.mulInt (sval s n) (toBall a) := by
  refine ball_ext ?_ ?_
  · simp only [mulInt, toBall_m, Ival.Ball.mulInt, bx_eq, nmul]
    rw [sval_xor]
  · simp [mulInt, Ival.Ball.mulInt]

theorem toBall_shr (k : Nat) (a : KBall) : toBall (shr k a) = Ival.Ball.shr k (toBall a) := by
  rw [shr, toBall_rndD]
  refine ball_ext ?_ ?_
  · simp [Ival.Ball.shr, rnd2_eq_rndN]
  · simp [Ival.Ball.shr]

theorem toBall_divNat (d : Nat) (a : KBall) : toBall (divNat d a) = Ival.Ball.divNat d (toBall a) := by
  rw [divNat, toBall_rndD]
  refine ball_ext ?_ ?_
  · simp [Ival.Ball.divNat]
  · simp [Ival.Ball.divNat]

theorem absHi_eq (a : KBall) : absHi a = Ival.Ball.absHi (toBall a) := by
  simp [absHi, Ival.Ball.absHi]

theorem isPos_eq (a : KBall) : isPos a = Ival.Ball.isPos (toBall a) := by
  cases h : a.s <;> simp [isPos, Ival.Ball.isPos, h, sval]

theorem isNeg_eq (a : KBall) : isNeg a = Ival.Ball.isNeg (toBall a) := by
  cases h : a.s <;> simp [isNeg, Ival.Ball.isNeg, h, sval]
  omega

theorem toBall_absB (a : KBall) : toBall (absB a) = Ival.Ball.absB (toBall a) := by
  refine ball_ext ?_ rfl
  simp [absB, Ival.Ball.absB]

/-! ## Taylor sums, `exp` -/

theorem toBall_taylorAux (P : Nat) (alt : Bool) (x : KBall) : ∀ (fuel j : Nat) (t ev od : KBall),
    Prod.map toBall toBall (taylorAux P alt x fuel j t ev od) =
      Ival.Ball.taylorAux P alt (toBall x) fuel j (toBall t) (toBall ev) (toBall od)
  | 0, j, t, ev, od => rfl
  | fuel + 1, j, t, ev, od => by
    simp only [taylorAux, Ival.Ball.taylorAux]
    rw [toBall_taylorAux P alt x fuel, toBall_divNat, toBall_mul]
    congr 1
    · by_cases h2 : j % 2 = 0 <;> by_cases h4 : j % 4 = 2 <;> cases alt <;>
        simp [h2, h4, toBall_add, toBall_sub]
    · by_cases h2 : j % 2 = 1 <;> by_cases h4 : j % 4 = 3 <;> cases alt <;>
        simp [h2, h4, toBall_add, toBall_sub]

theorem fact_eq : ∀ n, fact n = Ival.Ball.fact n
  | 0 => rfl
  | n + 1 => by simp [fact, Ival.Ball.fact, fact_eq n]

theorem remBound_eq (P n mh : Nat) : remBound P n mh = Ival.Ball.remBound P n mh := by
  simp [remBound, Ival.Ball.remBound, fact_eq]

lemma cond_and_false (a b : Bool) : cond a b false = (a && b) := by cases a <;> rfl

theorem toBall_expSmall (P n : Nat) (x : KBall) :
    (expSmall P n x).map toBall = Ival.Ball.expSmall P n (toBall x) := by
  unfold expSmall Ival.Ball.expSmall
  have hcond : cond (Nat.ble (absHi x) (Nat.pow 2 P)) (blt 0 n) false =
      decide (Ival.Ball.absHi (toBall x) ≤ 2 ^ P ∧ 0 < n) := by
    rw [cond_and_false, nble, npow, blt_eq, absHi_eq]
    simp
  have ht : Ival.Ball.taylorAux P false (toBall x) n 0 (Ival.Ball.ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩ =
      Prod.map toBall toBall (taylorAux P false x n 0 (ofInt P false 1) ⟨false, 0, 0⟩ ⟨false, 0, 0⟩) := by
    rw [toBall_taylorAux, toBall_ofInt]
    rfl
  rw [hcond]
  by_cases hc : Ival.Ball.absHi (toBall x) ≤ 2 ^ P ∧ 0 < n
  · simp only [hc, decide_true, Bool.cond_true, ite_true, and_self, ht, Prod.map, Option.map_some]
    set A := taylorAux P false x n 0 (ofInt P false 1) ⟨false, 0, 0⟩ ⟨false, 0, 0⟩
    have hS := toBall_add A.1 A.2
    congr 1
    apply ball_ext
    · have h1 := congrArg Ival.Ball.m hS
      exact h1
    · have h1 := congrArg Ival.Ball.r hS
      simp only [toBall_r] at h1
      simp only [toBall_r, nadd, remBound_eq, absHi_eq, h1]
  · simp only [hc, decide_false, Bool.cond_false, ite_false, Option.map_none]

theorem toBall_sqIter (P : Nat) : ∀ (k : Nat) (a : KBall), toBall (sqIter P k a) = Ival.Ball.sqIter P k (toBall a)
  | 0, a => rfl
  | k + 1, a => by simp only [sqIter, Ival.Ball.sqIter, toBall_sqIter P k, toBall_mul]

theorem findShift_eq (P h : Nat) : ∀ fuel k, findShift P h fuel k = Ival.Ball.findShift P h fuel k
  | 0, k => rfl
  | fuel + 1, k => by
    simp only [findShift, Ival.Ball.findShift, nble, nmul, npow, nadd, findShift_eq P h fuel]
    by_cases hc : 2 * h ≤ 2 ^ (P + k) <;> simp [hc]

/-- `Option.map` commutes with the simulation for maps. -/
lemma map_map_toBall {α : Type} (o : Option α) (f : α → KBall) (g : Ival.Ball → Ival.Ball) (f' : α → Ival.Ball)
    (hf : ∀ a, toBall (f a) = g (f' a)) : (o.map f).map toBall = (o.map f').map g := by
  cases o <;> simp [hf]

theorem toBall_expB (P n : Nat) (x : KBall) : (expB P n x).map toBall = Ival.Ball.expB P n (toBall x) := by
  dsimp only [expB, Ival.Ball.expB]
  rw [findShift_eq, absHi_eq, ← toBall_shr, ← toBall_expSmall]
  cases expSmall P n (shr (Ival.Ball.findShift P (Ival.Ball.absHi (toBall x)) 64 0) x) with
  | none => rfl
  | some e => simp [toBall_sqIter]

theorem toBall_expB' (P n : Nat) (x : KBall) : (expB' P n x).map toBall = Ival.Ball.expB' P n (toBall x) := by
  dsimp only [expB', Ival.Ball.expB']
  have hL : ((P : Int) * ((2 ^ P : Nat) : Int)) = ((P * 2 ^ P : Nat) : Int) := by push_cast; ring
  have hB := toBall_expB P n x
  obtain ⟨s, m, r⟩ := x
  simp only [Ival.Ball.hi, toBall_m, toBall_r, hL, nble, nbeq, nadd, nmul, npow]
  generalize P * 2 ^ P = L
  cases s
  · by_cases h : m + r + L = 0
    · have h' : sval false m + (r : Int) ≤ -(L : Int) := by simp; omega
      simp only [h, h', decide_true, Bool.cond_true, ite_true, Option.map_some, Bool.cond_false]
      rfl
    · have h' : ¬ (sval false m + (r : Int) ≤ -(L : Int)) := by simp; omega
      simp only [h, h', decide_false, Bool.cond_false, ite_false]
      exact hB
  · by_cases h : r + L ≤ m
    · have h' : sval true m + (r : Int) ≤ -(L : Int) := by simp; omega
      simp only [h, h', decide_true, Bool.cond_true, ite_true, Option.map_some]
      rfl
    · have h' : ¬ (sval true m + (r : Int) ≤ -(L : Int)) := by simp; omega
      simp only [h, h', decide_false, Bool.cond_false, Bool.cond_true, ite_false]
      exact hB

/-! ## Hull, `expH`, `π` -/

lemma sle_eq (s₁ : Bool) (a : Nat) (s₂ : Bool) (b : Nat) : sle s₁ a s₂ b = decide (sval s₁ a ≤ sval s₂ b) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [decide_eq_true_iff]
  cases s₁ <;> cases s₂ <;> simp [sle] <;> omega

lemma sval_cond (c : Bool) (x y : KBall) : sval (cond c x y).s (cond c x y).m = cond c (sval x.s x.m) (sval y.s y.m) := by
  cases c <;> rfl

lemma toNat_sval (k : KBall) : cond k.s 0 k.m = (sval k.s k.m).toNat := by
  cases k.s <;> simp

theorem toBall_hullB (a b : KBall) : toBall (hullB a b) = Ival.Ball.hullB (toBall a) (toBall b) := by
  dsimp only [hullB, Ival.Ball.hullB]
  -- values of the pieces
  set la := sadd a.s a.m true a.r 0 with hla
  set lb := sadd b.s b.m true b.r 0 with hlb
  set ha := sadd a.s a.m false a.r 0 with hha
  set hb := sadd b.s b.m false b.r 0 with hhb
  have vla : sval la.s la.m = (toBall a).lo := by rw [hla, sval_sadd]; simp [Ival.Ball.lo]; ring
  have vlb : sval lb.s lb.m = (toBall b).lo := by rw [hlb, sval_sadd]; simp [Ival.Ball.lo]; ring
  have vha : sval ha.s ha.m = (toBall a).hi := by rw [hha, sval_sadd]; simp [Ival.Ball.hi]
  have vhb : sval hb.s hb.m = (toBall b).hi := by rw [hhb, sval_sadd]; simp [Ival.Ball.hi]
  set lo := cond (sle la.s la.m lb.s lb.m) la lb with hlo
  set hi := cond (sle ha.s ha.m hb.s hb.m) hb ha with hhi
  have vlo : sval lo.s lo.m = min (toBall a).lo (toBall b).lo := by
    rw [hlo, sval_cond, sle_eq, vla, vlb, min_def]
    by_cases h : (toBall a).lo ≤ (toBall b).lo <;> simp [h]
  have vhi : sval hi.s hi.m = max (toBall a).hi (toBall b).hi := by
    rw [hhi, sval_cond, sle_eq, vha, vhb, max_def]
    by_cases h : (toBall a).hi ≤ (toBall b).hi <;> simp [h]
  set sm := sadd lo.s lo.m hi.s hi.m 0 with hsm
  have vsm : sval sm.s sm.m = min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi := by
    rw [hsm, sval_sadd, vlo, vhi]
  set c : KBall := cond sm.s ⟨true, Nat.div (Nat.add sm.m 1) 2, 0⟩ ⟨false, Nat.div sm.m 2, 0⟩ with hc
  have vc : sval c.s c.m = (min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi) / 2 := by
    rw [← vsm, hc]
    cases sm.s <;> simp <;> omega
  have vd1 : sval (sadd hi.s hi.m (cond c.s false true) c.m 0).s (sadd hi.s hi.m (cond c.s false true) c.m 0).m =
      max (toBall a).hi (toBall b).hi - (min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi) / 2 := by
    rw [sval_sadd, sval_not, vhi, vc]; ring
  have vd2 : sval (sadd c.s c.m (cond lo.s false true) lo.m 0).s (sadd c.s c.m (cond lo.s false true) lo.m 0).m =
      (min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi) / 2 - min (toBall a).lo (toBall b).lo := by
    rw [sval_sadd, sval_not, vlo, vc]; ring
  refine ball_ext ?_ ?_
  · exact vc
  · show cond (Nat.ble _ _) _ _ = _
    rw [toNat_sval, toNat_sval, vd1, vd2, nble]
    generalize max (toBall a).hi (toBall b).hi -
      (min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi) / 2 = x
    generalize (min (toBall a).lo (toBall b).lo + max (toBall a).hi (toBall b).hi) / 2 -
      min (toBall a).lo (toBall b).lo = y
    by_cases h : x.toNat ≤ y.toNat
    · have hxy : x ≤ y ∨ y.toNat = x.toNat := by omega
      simp only [h, decide_true, Bool.cond_true]
      rcases hxy with hxy | hxy
      · rw [max_eq_right hxy]
      · rcases le_total x y with h2 | h2
        · rw [max_eq_right h2]
        · rw [max_eq_left h2, hxy]
    · have hxy : y ≤ x := by
        by_contra hc
        exact h (Int.toNat_le_toNat (le_of_lt (not_le.1 hc)))
      simp only [h, decide_false, Bool.cond_false]
      rw [max_eq_left hxy]

/-- `Option.bind` commutes with the simulation. -/
lemma bind_toBall {α : Type} (o : Option KBall) (o' : Option Ival.Ball) (ho : o.map toBall = o')
    (f : KBall → Option α) (f' : Ival.Ball → Option α) (hf : ∀ a, f a = f' (toBall a)) :
    o.bind f = o'.bind f' := by
  subst ho
  cases o <;> simp [hf]

theorem toBall_expH (P n : Nat) (x : KBall) : (expH P n x).map toBall = Ival.Ball.expH P n (toBall x) := by
  unfold expH Ival.Ball.expH
  have h1 : (expB' P n (sadd x.s x.m true x.r 0)).map toBall = Ival.Ball.expB' P n ⟨(toBall x).m - (toBall x).r, 0⟩ := by
    rw [toBall_expB', toBall_sadd]; simp [sub_eq_add_neg]
  have h2 : (expB' P n (sadd x.s x.m false x.r 0)).map toBall = Ival.Ball.expB' P n ⟨(toBall x).m + (toBall x).r, 0⟩ := by
    rw [toBall_expB', toBall_sadd]; simp
  cases e1 : expB' P n (sadd x.s x.m true x.r 0) <;> cases e2 : expB' P n (sadd x.s x.m false x.r 0) <;>
    rw [e1] at h1 <;> rw [e2] at h2 <;> simp at h1 h2 <;> simp [← h1, ← h2, toBall_hullB]

theorem toBall_piB (P : Nat) : toBall (piB P) = Ival.Ball.piB P := by
  rw [piB, toBall_rndD]
  refine ball_ext ?_ ?_
  · simp [Ival.Ball.piB]
  · simp [Ival.Ball.piB]

/-! ## `cos`, `sin` -/

theorem toBall_cosSinSmall (P n : Nat) (θ : KBall) :
    (cosSinSmall P n θ).map (Prod.map toBall toBall) = Ival.Ball.cosSinSmall P n (toBall θ) := by
  unfold cosSinSmall Ival.Ball.cosSinSmall
  have hcond : cond (Nat.ble (absHi θ) (Nat.pow 2 P)) (blt 0 n) false =
      decide (Ival.Ball.absHi (toBall θ) ≤ 2 ^ P ∧ 0 < n) := by
    rw [cond_and_false, nble, npow, blt_eq, absHi_eq]
    simp
  have ht : Ival.Ball.taylorAux P true (toBall θ) n 0 (Ival.Ball.ofInt P 1) ⟨0, 0⟩ ⟨0, 0⟩ =
      Prod.map toBall toBall (taylorAux P true θ n 0 (ofInt P false 1) ⟨false, 0, 0⟩ ⟨false, 0, 0⟩) := by
    rw [toBall_taylorAux, toBall_ofInt]
    rfl
  rw [hcond]
  by_cases hc : Ival.Ball.absHi (toBall θ) ≤ 2 ^ P ∧ 0 < n
  · simp only [hc, decide_true, Bool.cond_true, ite_true, and_self, ht, Prod.map, Option.map_some]
    simp only [remBound_eq, absHi_eq, Prod.mk.injEq, Option.some.injEq]
    constructor <;> rfl
  · simp only [hc, decide_false, Bool.cond_false, ite_false, Option.map_none]

theorem toBall_dblIter (P : Nat) : ∀ (k : Nat) (cs : KBall × KBall),
    Prod.map toBall toBall (dblIter P k cs) = Ival.Ball.dblIter P k (Prod.map toBall toBall cs)
  | 0, cs => rfl
  | k + 1, cs => by
    simp only [dblIter, Prod.map, Ival.Ball.dblIter]
    have := toBall_dblIter P k (sub (mul P cs.1 cs.1) (mul P cs.2 cs.2), mulInt false 2 (mul P cs.1 cs.2))
    simp only [Prod.map] at this
    rw [this, toBall_sub, toBall_mul, toBall_mul, toBall_mulInt, toBall_mul]
    rfl

theorem toBall_fracTurn (P : Nat) (u : KBall) : toBall (fracTurn P u) = Ival.Ball.fracTurn P (toBall u) := by
  dsimp only [fracTurn, Ival.Ball.fracTurn]
  rw [toBall_sadd]
  refine ball_ext ?_ rfl
  have hq := sval_rndD u.s u.m (Nat.pow 2 P) 0
  simp only [sval_not, npow, nmul, toBall_m] at hq ⊢
  rw [rnd2_eq_rndN, ← hq]
  cases (rndD u.s u.m (2 ^ P) 0).s <;> simp only [sval, Bool.cond_true, Bool.cond_false] <;> push_cast <;> ring

theorem toBall_turnArg (P k : Nat) (u : KBall) : toBall (turnArg P k u) = Ival.Ball.turnArg P k (toBall u) := by
  simp only [turnArg, Ival.Ball.turnArg, toBall_shr, toBall_mul, toBall_mulInt, toBall_piB, toBall_fracTurn]
  rfl

theorem toBall_cosSinTurn (P n k : Nat) (u : KBall) :
    (cosSinTurn P n k u).map (Prod.map toBall toBall) = Ival.Ball.cosSinTurn P n k (toBall u) := by
  unfold cosSinTurn Ival.Ball.cosSinTurn
  rw [← toBall_turnArg, ← toBall_cosSinSmall]
  cases cosSinSmall P n (turnArg P k u) <;> simp [toBall_dblIter]

theorem toBall_cosSinTurnC (P n k : Nat) (u : KBall) :
    (cosSinTurnC P n k u).map (Prod.map toBall toBall) = Ival.Ball.cosSinTurnC P n k (toBall u) := by
  unfold cosSinTurnC Ival.Ball.cosSinTurnC
  have h := toBall_cosSinTurn P n k ⟨u.s, u.m, 0⟩
  rw [show toBall ⟨u.s, u.m, 0⟩ = ⟨(toBall u).m, 0⟩ from rfl] at h
  rw [← h]
  cases cosSinTurn P n k ⟨u.s, u.m, 0⟩ <;> simp
  constructor <;> rfl

end KBall
end KIval
