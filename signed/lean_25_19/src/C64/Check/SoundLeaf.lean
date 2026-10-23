import C64.Check.SoundArc
import C64.Check.SettleL

/-!
# Soundness of the checker, part 4: boxes of pinned values, exclusion leaves
-/

namespace C64Chk

open Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### Boxes -/

/-- The box `(d, i, k)` of the pin of radius `R`. -/
noncomputable def boxR (R : Q) (d i k : ℕ) : C64.Box :=
  ⟨R.val * (2 * (i : ℝ) - 2 ^ d) / 2 ^ d, R.val * (2 * (i : ℝ) + 2 - 2 ^ d) / 2 ^ d,
   R.val * (2 * (k : ℝ) - 2 ^ d) / 2 ^ d, R.val * (2 * (k : ℝ) + 2 - 2 ^ d) / 2 ^ d⟩

/-- The balls of a box contain its corners. -/
def Box4OK (P : ℕ) (Q : C64.Box) (B : Box4) : Prop :=
  mem P Q.x0 B.1 ∧ mem P Q.x1 B.2.1 ∧ mem P Q.y0 B.2.2.1 ∧ mem P Q.y1 B.2.2.2

theorem mem_boxCorner (R : Q) (hR : 0 < R.d) (d : ℕ) (a : ℤ) :
    mem P (R.val * (a : ℝ) / 2 ^ d) (Ball.ofRat P (R.n * a) (R.d * 2 ^ d)) := by
  have h := mem_ofRat P (R.n * a) (R.d * 2 ^ d) (Nat.mul_pos hR (by positivity))
  have e : ((R.n * a : ℤ) : ℝ) / ((R.d * 2 ^ d : ℕ) : ℝ) = R.val * (a : ℝ) / 2 ^ d := by
    unfold Q.val; push_cast
    have : (0 : ℝ) < R.d := by exact_mod_cast hR
    field_simp
  rw [e] at h; exact h

theorem boxB_ok (R : Q) (hR : 0 < R.d) (d i k : ℕ) : Box4OK P (boxR R d i k) (boxB P R d i k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mem_boxCorner (P := P) R hR d (2 * (i : ℤ) - 2 ^ d); push_cast at this; exact this
  · have := mem_boxCorner (P := P) R hR d (2 * (i : ℤ) + 2 - 2 ^ d); push_cast at this; exact this
  · have := mem_boxCorner (P := P) R hR d (2 * (k : ℤ) - 2 ^ d); push_cast at this; exact this
  · have := mem_boxCorner (P := P) R hR d (2 * (k : ℤ) + 2 - 2 ^ d); push_cast at this; exact this

theorem re_conj_cOf (y : ℤ × ℤ) (w : ℂ) : ((starRingEnd ℂ) (cOf y) * w).re = (y.1 : ℝ) * w.re + (y.2 : ℝ) * w.im := by
  simp [cOf, Complex.mul_re]

theorem boxBounds_ok {Q : C64.Box} {B : Box4} (hB : Box4OK P Q B) (y : ℤ × ℤ) :
    C64.BoxBounds (cOf y) Q ((boxLo y B : ℝ) / 2 ^ P) ((boxHi y B : ℝ) / 2 ^ P) := by
  intro w hw
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  rw [re_conj_cOf]
  obtain ⟨b1, b2, b3, b4⟩ := hB
  constructor
  · unfold boxLo
    have key : ∀ (yy : ℤ) (lo hi : ℝ) (Blo Bhi : Ball) (x : ℝ), lo ≤ x → x ≤ hi → mem P lo Blo → mem P hi Bhi →
        mem P ((yy : ℝ) * (if 0 ≤ yy then lo else hi)) (Ball.mulInt yy (if 0 ≤ yy then Blo else Bhi)) ∧
        (yy : ℝ) * (if 0 ≤ yy then lo else hi) ≤ (yy : ℝ) * x := by
      intro yy lo hi Blo Bhi x hlo hhi hBlo hBhi
      split_ifs with hy
      · exact ⟨mem_mulInt yy hBlo, mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hy)⟩
      · push Not at hy
        exact ⟨mem_mulInt yy hBhi, mul_le_mul_of_nonpos_left hhi (by exact_mod_cast hy.le)⟩
    obtain ⟨m1, l1⟩ := key y.1 Q.x0 Q.x1 B.1 B.2.1 w.re hx0 hx1 b1 b2
    obtain ⟨m2, l2⟩ := key y.2 Q.y0 Q.y1 B.2.2.1 B.2.2.2 w.im hy0 hy1 b3 b4
    have h := (mem_iff_lo_hi.1 (mem_add m1 m2)).1
    linarith
  · unfold boxHi
    have key : ∀ (yy : ℤ) (lo hi : ℝ) (Blo Bhi : Ball) (x : ℝ), lo ≤ x → x ≤ hi → mem P lo Blo → mem P hi Bhi →
        mem P ((yy : ℝ) * (if 0 ≤ yy then hi else lo)) (Ball.mulInt yy (if 0 ≤ yy then Bhi else Blo)) ∧
        (yy : ℝ) * x ≤ (yy : ℝ) * (if 0 ≤ yy then hi else lo) := by
      intro yy lo hi Blo Bhi x hlo hhi hBlo hBhi
      split_ifs with hy
      · exact ⟨mem_mulInt yy hBhi, mul_le_mul_of_nonneg_left hhi (by exact_mod_cast hy)⟩
      · push Not at hy
        exact ⟨mem_mulInt yy hBlo, mul_le_mul_of_nonpos_left hlo (by exact_mod_cast hy.le)⟩
    obtain ⟨m1, l1⟩ := key y.1 Q.x0 Q.x1 B.1 B.2.1 w.re hx0 hx1 b1 b2
    obtain ⟨m2, l2⟩ := key y.2 Q.y0 Q.y1 B.2.2.1 B.2.2.2 w.im hy0 hy1 b3 b4
    have h := (mem_iff_lo_hi.1 (mem_add m1 m2)).2
    linarith

/-- The root box is `[-R, R]²`. -/
theorem boxR_root (R : Q) {w : ℂ} (hre : |w.re| ≤ R.val) (him : |w.im| ≤ R.val) : (boxR R 0 0 0).mem w := by
  unfold boxR C64.Box.mem
  simp only [pow_zero, div_one, Nat.cast_zero, mul_zero, zero_sub, zero_add]
  obtain ⟨a1, a2⟩ := abs_le.1 hre
  obtain ⟨b1, b2⟩ := abs_le.1 him
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The four children cover the box. -/
theorem boxR_split (R : Q) (hR : 0 ≤ R.val) (d i k : ℕ) {w : ℂ} (hw : (boxR R d i k).mem w) :
    ∃ n < 4, (boxR R (kid (d, i, k) n).1 (kid (d, i, k) n).2.1 (kid (d, i, k) n).2.2).mem w := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
  have hd : (0 : ℝ) < 2 ^ d := by positivity
  set mx := R.val * (2 * (i : ℝ) + 1 - 2 ^ d) / 2 ^ d
  set my := R.val * (2 * (k : ℝ) + 1 - 2 ^ d) / 2 ^ d
  -- the children's corners at depth d + 1
  have c1 : ∀ j : ℕ, R.val * (2 * ((2 * j : ℕ) : ℝ) - 2 ^ (d + 1)) / 2 ^ (d + 1) = R.val * (2 * (j : ℝ) - 2 ^ d) / 2 ^ d := by
    intro j; push_cast; rw [pow_succ]; field_simp; try ring
  have c2 : ∀ j : ℕ, R.val * (2 * ((2 * j : ℕ) : ℝ) + 2 - 2 ^ (d + 1)) / 2 ^ (d + 1) =
      R.val * (2 * (j : ℝ) + 1 - 2 ^ d) / 2 ^ d := by
    intro j; push_cast; rw [pow_succ]; field_simp; try ring
  have c3 : ∀ j : ℕ, R.val * (2 * ((2 * j + 1 : ℕ) : ℝ) - 2 ^ (d + 1)) / 2 ^ (d + 1) =
      R.val * (2 * (j : ℝ) + 1 - 2 ^ d) / 2 ^ d := by
    intro j; push_cast; rw [pow_succ]; field_simp; try ring
  have c4 : ∀ j : ℕ, R.val * (2 * ((2 * j + 1 : ℕ) : ℝ) + 2 - 2 ^ (d + 1)) / 2 ^ (d + 1) =
      R.val * (2 * (j : ℝ) + 2 - 2 ^ d) / 2 ^ d := by
    intro j; push_cast; rw [pow_succ]; field_simp; try ring
  rcases le_total w.re mx with hxm | hxm <;> rcases le_total w.im my with hym | hym
  · refine ⟨0, by norm_num, ?_⟩
    simp only [kid, Nat.zero_mod, Nat.zero_div, add_zero]
    unfold boxR C64.Box.mem; simp only
    rw [c1, c2, c1, c2]; exact ⟨hx0, hxm, hy0, hym⟩
  · refine ⟨2, by norm_num, ?_⟩
    simp only [kid, show (2 : ℕ) % 2 = 0 from rfl, show (2 : ℕ) / 2 = 1 from rfl, add_zero]
    unfold boxR C64.Box.mem; simp only
    rw [c1, c2, c3, c4]; exact ⟨hx0, hxm, hym, hy1⟩
  · refine ⟨1, by norm_num, ?_⟩
    simp only [kid, show (1 : ℕ) % 2 = 1 from rfl, show (1 : ℕ) / 2 = 0 from rfl, add_zero]
    unfold boxR C64.Box.mem; simp only
    rw [c3, c4, c1, c2]; exact ⟨hxm, hx1, hy0, hym⟩
  · refine ⟨3, by norm_num, ?_⟩
    simp only [kid, show (3 : ℕ) % 2 = 1 from rfl, show (3 : ℕ) / 2 = 1 from rfl]
    unfold boxR C64.Box.mem; simp only
    rw [c3, c4, c3, c4]; exact ⟨hxm, hx1, hym, hy1⟩


/-! ### Arc contexts and pin lists -/

/-- Semantic content of an arc context: `z_c`, and the pinned points `ps`. -/
structure ACtxOK (g : Glob) (A : ACtx) (zc : ℂ) (ps : List ℂ) : Prop where
  hzc : memC g.P zc A.zc
  hSc : memC g.P (C64.S zc) A.Sc
  hS1c : memC g.P (C64.S1 zc) A.S1c
  hzT : PtOK g.P g.D zc A.zT
  hpins : List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧ 0 < pb.2.2.d)
    ps A.pins

/-- The pins with their boxes. -/
noncomputable def pqL : List ℂ → List (CBall × PtT × Q) → List (ℕ × ℕ × ℕ) → List (ℂ × C64.Box)
  | p :: ps, pb :: pins, b :: bx => (p, boxR pb.2.2 b.1 b.2.1 b.2.2) :: pqL ps pins bx
  | _, _, _ => []

/-- The pin data of a leaf with multipliers `ys`. -/
noncomputable def dsOf (P : ℕ) : List ℂ → List (CBall × PtT × Q) → List (ℕ × ℕ × ℕ) → List (ℤ × ℤ) →
    List C64.PinD
  | p :: ps, pb :: pins, b :: bx, y :: ys =>
    ⟨p, boxR pb.2.2 b.1 b.2.1 b.2.2, cOf y, (boxLo y (boxB P pb.2.2 b.1 b.2.1 b.2.2) : ℝ) / 2 ^ P,
      (boxHi y (boxB P pb.2.2 b.1 b.2.1 b.2.2) : ℝ) / 2 ^ P⟩ :: dsOf P ps pins bx ys
  | _, _, _, _ => []

theorem rdPairs_length : ∀ (m s : ℕ), (rdPairs m s).1.length = m
  | 0, _ => rfl
  | m + 1, s => by simp [rdPairs, rdPairs_length m]

theorem pqOf_dsOf : ∀ (ps : List ℂ) (pins : List (CBall × PtT × Q)) (bx : List (ℕ × ℕ × ℕ)) (ys : List (ℤ × ℤ)),
    pins.length = ps.length → bx.length = ps.length → ys.length = ps.length →
    C64.pqOf (dsOf P ps pins bx ys) = pqL ps pins bx
  | [], _, _, _, _, _, _ => by cases ‹List (CBall × PtT × Q)› <;> rfl
  | p :: ps, pb :: pins, b :: bx, y :: ys, h1, h2, h3 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
    simp [dsOf, pqL, C64.pqOf, pqOf_dsOf ps pins bx ys h1 h2 h3] at *
    exact pqOf_dsOf ps pins bx ys h1 h2 h3
  | _ :: _, [], _, _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, h3 => by simp at h3

theorem dsOf_bounds {ps : List ℂ} {pins : List (CBall × PtT × Q)} (hpins : ∀ pb ∈ pins, 0 < pb.2.2.d) :
    ∀ (bx : List (ℕ × ℕ × ℕ)) (ys : List (ℤ × ℤ)), ∀ d ∈ dsOf P ps pins bx ys, C64.BoxBounds d.y d.Q d.lo d.hi := by
  induction ps generalizing pins with
  | nil => intro bx ys d hd; simp [dsOf] at hd
  | cons p ps ih =>
    intro bx ys d hd
    match pins, bx, ys, hd with
    | pb :: pins, b :: bx, y :: ys, hd =>
      simp only [dsOf, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact boxBounds_ok (boxB_ok pb.2.2 (hpins pb (by simp)) _ _ _) y
      · exact ih (fun q hq => hpins q (by simp [hq])) bx ys d hd

theorem sum_lo_dsOf : ∀ (ps : List ℂ) (pins : List (CBall × PtT × Q)) (bx : List (ℕ × ℕ × ℕ)) (ys : List (ℤ × ℤ)),
    pins.length = ps.length → bx.length = ps.length →
    ((dsOf P ps pins bx ys).map fun d => d.lo).sum = (sumBox false (pinBoxes P pins bx) ys : ℝ) / 2 ^ P ∧
    ((dsOf P ps pins bx ys).map fun d => d.hi).sum = (sumBox true (pinBoxes P pins bx) ys : ℝ) / 2 ^ P
  | [], [], [], _, _, _ => by simp [dsOf, pinBoxes, sumBox]
  | p :: ps, pb :: pins, b :: bx, [], _, _ => by
    obtain ⟨d, i, k⟩ := b; simp [dsOf, pinBoxes, sumBox]
  | p :: ps, pb :: pins, b :: bx, y :: ys, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    obtain ⟨i1, i2⟩ := sum_lo_dsOf ps pins bx ys h1 h2
    obtain ⟨d, i, k⟩ := b
    simp only [dsOf, pinBoxes, sumBox, List.map_cons, List.sum_cons, i1, i2, Bool.false_eq_true, if_false,
      if_true]
    push_cast; constructor <;> ring
  | [], _ :: _, _, _, h1, _ => by simp at h1
  | [], [], _ :: _, _, _, h2 => by simp at h2
  | _ :: _, [], _, _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2 => by simp at h2

/-- The semantic terms of `yTerms`. -/
def yczs (neg : Bool) : List ℂ → List (ℤ × ℤ) → List (ℂ × ℂ)
  | p :: ps, y :: ys =>
    if y.1 = 0 ∧ y.2 = 0 then yczs neg ps ys
    else ((if neg then -(starRingEnd ℂ) (cOf y) else (starRingEnd ℂ) (cOf y)), p) :: yczs neg ps ys
  | _, _ => []

theorem yTerms_ok {g : Glob} {ps : List ℂ} {pins : List (CBall × PtT × Q)}
    (hpins : List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧ 0 < pb.2.2.d)
      ps pins) (neg : Bool) :
    ∀ ys : List (ℤ × ℤ), List.Forall₂ (fun cz T => TermOK g.P 0 1 cz.1 cz.2 T) (yczs neg ps ys) (yTerms g.P neg pins ys) ∧
      ∀ T ∈ yTerms g.P neg pins ys, T.st.length = g.D := by
  induction hpins with
  | nil => intro ys; cases ys <;> simp [yczs, yTerms]
  | @cons p pb ps pins hp _ ih =>
    intro ys
    cases ys with
    | nil => simp [yczs, yTerms]
    | cons y ys =>
      obtain ⟨i1, i2⟩ := ih ys
      simp only [yczs, yTerms]
      by_cases hy : y.1 = 0 ∧ y.2 = 0
      · rw [if_pos hy, if_pos hy]; exact ⟨i1, i2⟩
      · rw [if_neg hy, if_neg hy]
        refine ⟨List.Forall₂.cons (termOf_ok hp.2.1 ?_) i1, ?_⟩
        · cases neg
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact C64Num.CBall.memC_conj (memC_intC y)
          · simp only [↓reduceIte]
            exact C64Num.CBall.memC_neg (C64Num.CBall.memC_conj (memC_intC y))
        · intro T hT
          simp only [List.mem_cons] at hT
          rcases hT with rfl | hT
          · exact hp.2.1.len
          · exact i2 T hT

theorem fsum_yczs {P : ℕ} : ∀ (ps : List ℂ) (pins : List (CBall × PtT × Q)) (bx : List (ℕ × ℕ × ℕ))
    (ys : List (ℤ × ℤ)), pins.length = ps.length → bx.length = ps.length → ∀ t : ℝ,
    fsum (yczs false ps ys) t = ((dsOf P ps pins bx ys).map fun d => ((starRingEnd ℂ) d.y * C64.Kt t d.p).re).sum ∧
    fsum (yczs true ps ys) t = -((dsOf P ps pins bx ys).map fun d => ((starRingEnd ℂ) d.y * C64.Kt t d.p).re).sum
  | [], _, _, _, _, _, t => by cases ‹List (ℤ × ℤ)› <;> simp [yczs, dsOf, fsum]
  | p :: ps, pb :: pins, b :: bx, [], _, _, t => by simp [yczs, dsOf, fsum]
  | p :: ps, pb :: pins, b :: bx, y :: ys, h1, h2, t => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    obtain ⟨i1, i2⟩ := fsum_yczs (P := P) ps pins bx ys h1 h2 t
    simp only [yczs, dsOf, List.map_cons, List.sum_cons]
    by_cases hy : y.1 = 0 ∧ y.2 = 0
    · rw [if_pos hy, if_pos hy]
      have : cOf y = 0 := by
        unfold cOf; rw [hy.1, hy.2]; apply Complex.ext <;> simp
      rw [i1, i2, this]; simp
    · rw [if_neg hy, if_neg hy]
      refine ⟨?_, ?_⟩
      · simp only [fsum, List.map_cons, List.sum_cons, Bool.false_eq_true, ↓reduceIte] at i1 ⊢
        rw [i1]
      · simp only [fsum, List.map_cons, List.sum_cons, ↓reduceIte] at i2 ⊢
        rw [i2]; simp only [neg_mul, Complex.neg_re]; ring
  | _ :: _, [], _, _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2, _ => by simp at h2

theorem pins_d {g : Glob} {ps : List ℂ} {pins : List (CBall × PtT × Q)}
    (h : List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧ 0 < pb.2.2.d)
      ps pins) : ∀ pb ∈ pins, 0 < pb.2.2.d := by
  induction h with
  | nil => simp
  | cons hq _ ih =>
    intro pb hpb
    simp only [List.mem_cons] at hpb
    rcases hpb with rfl | hpb
    · exact hq.2.2
    · exact ih pb hpb

/-! ### Exclusion leaves -/

theorem checkExcl_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    {bx : List (ℕ × ℕ × ℕ)} (hbx : bx.length = ps.length) {dat : ℕ} (h : checkExcl g A bx dat = true) :
    C64.LeafSettledL g.tau.val zc ((A.r : ℝ) / 2 ^ g.P) (pqL ps A.pins bx) := by
  unfold checkExcl exclOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hX, hLb⟩, htb⟩ := h
  set vv := (rdPair dat).1
  set ys := (rdPairs A.pins.length (rdPair dat).2).1
  have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
  have hys : ys.length = ps.length := by rw [rdPairs_length, hlen]
  set ds := dsOf g.P ps A.pins bx ys
  have hpq : C64.pqOf ds = pqL ps A.pins bx := pqOf_dsOf ps A.pins bx ys hlen hbx hys
  rw [← hpq]
  have hP := two_pow_pos' g.P
  have hpd : ∀ pb ∈ A.pins, 0 < pb.2.2.d := pins_d hA.hpins
  have hbox := dsOf_bounds (P := g.P) (ps := ps) hpd bx ys
  obtain ⟨hlo, -⟩ := sum_lo_dsOf (P := g.P) ps A.pins bx ys hlen hbx
  set v : ℂ := cOf vv
  have hv := memC_intC (P := g.P) vv
  obtain ⟨hXlo, -⟩ := reConj_bounds hv hA.hSc
  -- 0 ≤ Re(v̄ S(z_c))
  have hX' : 0 ≤ ((starRingEnd ℂ) v * C64.S zc).re := by
    rcases hX with hX | hX
    · exact le_trans (div_nonneg (by exact_mod_cast hX) hP.le) hXlo
    · have : v = 0 := by
        simp only [v, hX, cOf]; apply Complex.ext <;> simp
      rw [this]; simp
  -- the right-hand side is at least lbE / 2^P
  have hrv : ‖v‖ * ((A.r : ℝ) / 2 ^ g.P) ≤ (mulU g.P (normHi (intC g.P vv)) A.r : ℝ) / 2 ^ g.P :=
    mulU_le (norm_nonneg _) (by positivity) (norm_le_normHi hv) le_rfl
  have hRHS : (lbE g A (pinBoxes g.P A.pins bx) vv ys : ℝ) / 2 ^ g.P ≤
      ((starRingEnd ℂ) v * C64.S zc).re - ‖v‖ * ((A.r : ℝ) / 2 ^ g.P) + (ds.map fun d => d.lo).sum := by
    rw [hlo]
    unfold lbE
    push_cast
    rw [add_div, sub_div]
    linarith
  have hEpos : 0 < ((starRingEnd ℂ) v * C64.S zc).re - ‖v‖ * ((A.r : ℝ) / 2 ^ g.P) + (ds.map fun d => d.lo).sum :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast hLb) hP) hRHS
  refine C64.leafSettledL_of_exclusion (tau_pos hg).le hbox hX' (fun t ht => ?_) hEpos
  -- the t-bound
  obtain ⟨hF, hL⟩ := yTerms_ok hA.hpins false ys
  have htb' := tbound_ok (czs := ((starRingEnd ℂ) v, zc) :: yczs false ps ys) htb
    (List.Forall₂.cons (termOf_ok hA.hzT (C64Num.CBall.memC_conj hv)) hF)
    (by
      intro T hT
      simp only [List.mem_cons] at hT
      rcases hT with rfl | hT
      · exact hA.hzT.len
      · exact hL T hT) t ht
  have hfs : fsum (((starRingEnd ℂ) v, zc) :: yczs false ps ys) t = C64.LamL v zc ds t := by
    unfold C64.LamL
    rw [show fsum (((starRingEnd ℂ) v, zc) :: yczs false ps ys) t =
      ((starRingEnd ℂ) v * C64.Kt t zc).re + fsum (yczs false ps ys) t by simp [fsum]]
    rw [(fsum_yczs (P := g.P) ps A.pins bx ys hlen hbx t).1]
  rw [hfs] at htb'
  have htn : 0 < g.tau.n.toNat := by have := hg.tn; omega
  have htd : 0 < g.tau.d := by have := lt_trans hg.tn hg.tlt; omega
  have hfl := floor_target_le hLb htn htd
  rw [tau_eq hg]
  have hτ : (0 : ℝ) < (g.tau.n.toNat : ℝ) / g.tau.d := by
    have : (0 : ℝ) < g.tau.n.toNat := by exact_mod_cast htn
    have : (0 : ℝ) < g.tau.d := by exact_mod_cast htd
    positivity
  calc ((g.tau.n.toNat : ℝ) / g.tau.d) * C64.LamL v zc ds t
      < ((g.tau.n.toNat : ℝ) / g.tau.d) *
        (((((lbE g A (pinBoxes g.P A.pins bx) vv ys).toNat * g.tau.d / g.tau.n.toNat : ℕ) : ℤ) : ℝ) / 2 ^ g.P) :=
        mul_lt_mul_of_pos_left htb' hτ
    _ = (((g.tau.n.toNat : ℝ) / g.tau.d) *
        (((lbE g A (pinBoxes g.P A.pins bx) vv ys).toNat * g.tau.d / g.tau.n.toNat : ℕ) : ℝ)) / 2 ^ g.P := by
        rw [Int.cast_natCast]; ring
    _ ≤ (lbE g A (pinBoxes g.P A.pins bx) vv ys : ℝ) / 2 ^ g.P := div_le_div_of_nonneg_right hfl hP.le
    _ ≤ _ := hRHS

end C64Chk
