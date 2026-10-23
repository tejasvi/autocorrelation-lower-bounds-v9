import C64K.KChkSim

/-! Simulation lemmas, part 2: the crossing radius, the arc context, the leaves, the arcs. -/

namespace C64KChk

open KIval KIval.KBall KNum KNum.KCBall C64Chk

lemma cfg_toC (g : Glob) : (⟨g.P, g.n, g.k⟩ : KNum.Cfg).toC = g.cfg := rfl

lemma expPiHi_add (c : KNum.Cfg) (x : KBall) (d : Nat) :
    expPiHi c (Nat.add (absHi x) d) = C64Chk.expPiHi c.toC ((toBall x).absHi + d) := by
  rw [expPiHi_eq, absHi_eq]; rfl

lemma rDisc_eq (g : Glob) (T1 : EllB) (tn td s0 s1 sc : Nat) (zc Sc S1c : KCBall) :
    rDisc g T1 tn td s0 s1 sc zc Sc S1c = C64Chk.rDisc g (toE T1) tn td s0 s1 sc (toC zc) (toC Sc) (toC S1c) := by
  unfold rDisc C64Chk.rDisc
  rw [ellSp_eq, toBall_pieceB, cfg_toC]
  refine bind_eq' rfl fun sp => ?_
  rw [lsLoc_eq, dOf_eq, cfg_toC]
  refine bind_eq' rfl fun L => ?_
  rw [SI.lt_eq, mSOf_eq, SI.toInt_ofNat, Nat.cast_zero, expPiHi_add, cfg_toC, Bool.cond_decide]
  by_cases h : 0 < C64Chk.mSOf g.P (toC Sc) (C64Chk.dOf g.P g.ES sp s0 s1 sc) L
  · simp only [h, ↓reduceIte]
    congr 1
    funext eY
    rw [rOf_eq, mSOf_eq]
  · simp only [h, ↓reduceIte]

lemma rBound_eq (g : Glob) (T1 : EllB) (tn td s0 s1 sc : Nat) (zc Sc S1c : KCBall) (rX : Nat) :
    rBound g T1 tn td s0 s1 sc zc Sc S1c rX =
      C64Chk.rBound g (toE T1) tn td s0 s1 sc (toC zc) (toC Sc) (toC S1c) rX := by
  unfold rBound C64Chk.rBound
  rw [rDisc_eq]
  congr 1
  funext r1
  exact nmax_eq r1 rX

/-! ## Arc context, pins, boxes -/

def toPin (p : KCBall × PtT × Q) : C64Num.CBall × C64Chk.PtT × Q := (toC p.1, toPt p.2.1, p.2.2)

def toAC (A : ACtx) : C64Chk.ACtx :=
  ⟨toE A.E1, A.s0, A.s1, A.sc, toC A.zc, toC A.Sc, toC A.S1c, toPt A.zT, A.r, A.pins.map toPin⟩

lemma pinBoxes_eq (P : Nat) : ∀ (pins : List (KCBall × PtT × Q)) (bs : List (Nat × Nat × Nat)),
    (pinBoxes P pins bs).map toB4 = C64Chk.pinBoxes P (pins.map toPin) bs
  | [], _ => by simp [pinBoxes, C64Chk.pinBoxes]
  | _ :: _, [] => by simp [pinBoxes, C64Chk.pinBoxes]
  | p :: ps, b :: bs => by
    obtain ⟨d, i, k⟩ := b
    simp only [pinBoxes, C64Chk.pinBoxes, List.map_cons]
    rw [boxB_eq, pinBoxes_eq P ps bs]
    rfl

lemma isZ2_eq (y : Int × Int) : isZ2 y = decide (y.1 = 0 ∧ y.2 = 0) := by
  unfold isZ2
  simp [Int.natAbs_eq_zero]

lemma beq_zero2 (y : Int × Int) : (y == (0, 0)) = decide (y.1 = 0 ∧ y.2 = 0) := by
  obtain ⟨a, b⟩ := y
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

lemma yTerms_eq (P : Nat) (neg : Bool) : ∀ (pins : List (KCBall × PtT × Q)) (ys : List (Int × Int)),
    (yTerms P neg pins ys).map toTm = C64Chk.yTerms P neg (pins.map toPin) ys
  | [], _ => by simp [yTerms, C64Chk.yTerms]
  | _ :: _, [] => by simp [yTerms, C64Chk.yTerms]
  | p :: ps, y :: ys => by
    simp only [yTerms, C64Chk.yTerms, List.map_cons, isZ2_eq, Bool.cond_decide]
    by_cases h : y.1 = 0 ∧ y.2 = 0
    · simp only [h, and_self, ↓reduceIte]
      exact yTerms_eq P neg ps ys
    · simp only [h, ↓reduceIte, List.map_cons]
      rw [yTerms_eq P neg ps ys]
      congr 1
      cases neg <;> simp [termOf_eq, toC_conj, toC_neg, toC_intC, toPin]

lemma sumBox_eq (hi : Bool) : ∀ (B : List Box4) (ys : List (Int × Int)),
    SI.toInt (sumBox hi B ys) = C64Chk.sumBox hi (B.map toB4) ys
  | [], _ => by simp [sumBox, C64Chk.sumBox]
  | _ :: _, [] => by simp [sumBox, C64Chk.sumBox]
  | b :: bs, y :: ys => by
    simp only [sumBox, C64Chk.sumBox, List.map_cons, SI.toInt_add]
    rw [sumBox_eq hi bs ys]
    cases hi
    · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte, boxLo_eq]
    · simp only [Bool.cond_true, ↓reduceIte, boxHi_eq]

/-! ## Exclusion leaves -/

lemma lbE_eq (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) :
    SI.toInt (lbE g A B v ys) = C64Chk.lbE g (toAC A) (B.map toB4) v ys := by
  unfold lbE C64Chk.lbE
  rw [SI.toInt_add, SI.toInt_sub, reConjLo_eq, toC_intC, SI.toInt_ofNat, normHi_eq, toC_intC, sumBox_eq]
  rfl

lemma exclOK_eq (g : Glob) (A : ACtx) (B : List Box4) (v : Int × Int) (ys : List (Int × Int)) :
    exclOK g A B v ys = C64Chk.exclOK g (toAC A) (B.map toB4) v ys := by
  unfold exclOK C64Chk.exclOK
  rw [tbound_eq, SI.nonneg_eq, reConjLo_eq, toC_intC, isZ2_eq, beq_zero2, SI.lt_eq, lbE_eq, SI.toInt_ofNat,
    SI.toInt_ofNat, SI.toNat_eq, lbE_eq, List.map_cons, termOf_eq, toC_conj, toC_intC, yTerms_eq]
  rfl

lemma checkExcl_eq (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) :
    checkExcl g A bx dat = C64Chk.checkExcl g (toAC A) bx dat := by
  unfold checkExcl C64Chk.checkExcl
  rw [exclOK_eq, pinBoxes_eq]
  simp only [toAC, List.length_map]

/-! ## Witness leaves: tile arcs -/

lemma aTA_eq (g : Glob) (A : ACtx) (r' : Nat) (u v : KCBall) (hiY : SI) (pd : PieceD) :
    SI.toInt (aTA g A r' u v hiY pd) = C64Chk.aTA g (toAC A) r' (toC u) (toC v) (SI.toInt hiY) (toPD pd) := by
  unfold aTA C64Chk.aTA
  rw [SI.toInt_sub, SI.toInt_sub, SI.toInt_sub, aLow_eq, reConjHi_eq, SI.toInt_ofNat, normHi_eq]
  rfl

lemma taPieceOK_eq (g : Glob) (A : ACtx) (r' tn td : Nat) (u v : KCBall) (yts : List TermS) (hiY : SI)
    (pd : PieceD) (T : PtT) :
    taPieceOK g A r' tn td u v yts hiY pd T =
      C64Chk.taPieceOK g (toAC A) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) (toPD pd) (toPt T) := by
  unfold taPieceOK C64Chk.taPieceOK
  rw [tbound_eq, SI.lt_eq, aTA_eq, tgt_eq, aTA_eq, dPof_eq, SI.toInt_ofNat, List.map_cons, List.map_cons,
    termOf_eq, termOf_eq, toC_conj, toC_neg, toC_conj]
  rfl

lemma checkTAPiece_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY : SI) (n0 n1 e : Nat) :
    checkTAPiece g A E r' tn td u v yts hiY n0 n1 e =
      C64Chk.checkTAPiece g (toAC A) (toE E) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) n0 n1 e := by
  unfold checkTAPiece C64Chk.checkTAPiece
  exact any_sim (pieceD_eq _ E n0 n1 e) fun pd => any_sim (ptT_eq _ g.D pd.z) fun T =>
    taPieceOK_eq g A r' tn td u v yts hiY pd T

lemma checkTA_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (u v : KCBall) (yts : List TermS)
    (hiY : SI) : ∀ (fuel n0 n1 e : Nat),
    checkTA g A E r' tn td u v yts hiY fuel n0 n1 e =
      C64Chk.checkTA g (toAC A) (toE E) r' tn td (toC u) (toC v) (yts.map toTm) (SI.toInt hiY) fuel n0 n1 e
  | 0, n0, n1, e => checkTAPiece_eq g A E r' tn td u v yts hiY n0 n1 e
  | fuel + 1, n0, n1, e => by
    simp only [checkTA, C64Chk.checkTA, nmul, nadd]
    rw [checkTAPiece_eq, checkTA_eq g A E r' tn td u v yts hiY fuel, checkTA_eq g A E r' tn td u v yts hiY fuel]

lemma taOK_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) (q0 q1 : Nat) (u v : Int × Int)
    (ys : List (Int × Int)) :
    taOK g A E r' tn td B q0 q1 u v ys = C64Chk.taOK g (toAC A) (toE E) r' tn td (B.map toB4) q0 q1 u v ys := by
  unfold taOK C64Chk.taOK
  rw [checkTA_eq, SI.le_eq, reConjHi_eq, SI.toInt_ofNat, toC_intC, toC_intC, isZ2_eq, beq_zero2,
    yTerms_eq, sumBox_eq, blt_eq, nble, npow]
  rfl

lemma checkTAs_eq (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) : ∀ (N q0 s : Nat),
    checkTAs g A E r' tn td B N q0 s = C64Chk.checkTAs g (toAC A) (toE E) r' tn td (B.map toB4) N q0 s
  | 0, _, _ => rfl
  | N + 1, q0, s => by
    simp only [checkTAs, C64Chk.checkTAs]
    rw [taOK_eq, checkTAs_eq g A E r' tn td B N]
    simp only [toAC, List.length_map, nbeq, npow]
    rfl

/-! ## Witness measures and winding numbers -/

lemma sumK_eq (c : KNum.Cfg) (z : KCBall) : ∀ as : List (Q × Q),
    (sumK c z as).map toC = C64Chk.sumK c.toC (toC z) as
  | [] => rfl
  | a :: as => by
    obtain ⟨t, m⟩ := a
    simp only [sumK, C64Chk.sumK]
    have hk := toC_ckt c (qBall c.P t) z
    rw [toBall_qBall] at hk
    refine bind_sim hk fun k => ?_
    refine map_sim (sumK_eq c z as) fun sm => ?_
    rw [toC_add, toC_mulR, toBall_qBall]
    rfl

lemma label_eq (gm : KCBall) (thr : Nat) : label gm thr = C64Chk.label (toC gm) (thr : Int) := by
  unfold label C64Chk.label
  simp only [SI.lt_eq, SI.toInt_ofNat, SI.toInt_add, loS_eq, hiS_eq, toC_re, toC_im, Nat.cast_zero,
    Bool.cond_decide]
  rfl

lemma windPiece_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum n0 n1 e : Nat) :
    windPiece c E as mSum n0 n1 e = C64Chk.windPiece c.toC (toE E) as mSum n0 n1 e := by
  unfold windPiece C64Chk.windPiece
  refine bind_sim' (pieceD_eq c E n0 n1 e) fun pd => ?_
  refine bind_sim' (sumK_eq c pd.z as) fun wk => ?_
  rw [label_eq, toC_sub, piHi_eq]
  rfl

lemma wind_eq (c : KNum.Cfg) (E : EllB) (as : List (Q × Q)) (mSum : Nat) : ∀ (fuel skip n0 n1 e : Nat),
    wind c E as mSum fuel skip n0 n1 e = C64Chk.wind c.toC (toE E) as mSum fuel skip n0 n1 e
  | 0, _, _, _, _ => rfl
  | fuel + 1, skip, n0, n1, e => by
    simp only [wind, C64Chk.wind]
    rw [wind_eq c E as mSum fuel, wind_eq c E as mSum fuel, windPiece_eq]
    simp only [nbeq, nsub, nmul, nadd, Bool.cond_decide]

lemma windOdd_eq (g : Glob) (E : EllB) (as : List (Q × Q)) (mSum : Nat) :
    windOdd g E as mSum = C64Chk.windOdd g (toE E) as mSum := by
  unfold windOdd C64Chk.windOdd
  rw [wind_eq]
  rfl

/-! ## Witness leaves -/

lemma tileOf_eq (g : Glob) (i : Nat) : (tileOf g i).map toE = C64Chk.tileOf g i := by
  unfold tileOf C64Chk.tileOf
  rw [Option.map_map]
  congr 1
  funext e
  exact toE_ellOf g.P e

lemma pinsIn_eq (c : KNum.Cfg) (as : List (Q × Q)) : ∀ (pins : List (KCBall × PtT × Q)) (B : List Box4),
    pinsIn c as pins B = C64Chk.pinsIn c.toC as (pins.map toPin) (B.map toB4)
  | [], _ => by simp [pinsIn, C64Chk.pinsIn]
  | _ :: _, [] => by simp [pinsIn, C64Chk.pinsIn]
  | p :: ps, b :: bs => by
    simp only [pinsIn, C64Chk.pinsIn, List.map_cons]
    rw [pinsIn_eq c as ps bs, any_sim (sumK_eq c p.1 as) (p' := fun w => C64Chk.inBox w (toB4 b))
      fun w => inBox_eq w b]
    rfl

lemma witBall_eq (g : Glob) (A : ACtx) (B : List Box4) (E : EllB) (w : WitD) (mn : Int) (md r' : Nat)
    (wz : KCBall) :
    witBall g A B E w mn md r' wz = C64Chk.witBall g (toAC A) (B.map toB4) (toE E) w mn md r' (toC wz) := by
  unfold witBall C64Chk.witBall
  rw [pinsIn_eq, checkTAs_eq, windOdd_eq, normHi_eq, toC_sub, toC_mulR, toBall_qBall]
  simp only [nble, npow, nmul, cdiv_eq]
  rfl

lemma witOK_eq (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) :
    witOK g A bx w = C64Chk.witOK g (toAC A) bx w := by
  unfold witOK C64Chk.witOK
  refine any_sim (tileOf_eq g w.ti) fun E => ?_
  refine any_eq rfl fun mm => ?_
  congr 1
  rw [rBound_eq]
  refine any_eq rfl fun r' => ?_
  refine any_sim (sumK_eq _ A.zc w.as) fun wz => ?_
  rw [witBall_eq, pinBoxes_eq]
  rfl

lemma checkWit_eq (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (dat : Nat) :
    checkWit g A bx dat = C64Chk.checkWit g (toAC A) bx dat := witOK_eq g A bx (rdWit dat)

/-! ## Type H arcs -/

lemma walk_eq (g : Glob) (A : ACtx) : ∀ (t : Tree) (bx : List (Nat × Nat × Nat)),
    walk g A t bx = C64Chk.walk g (toAC A) t bx
  | .excl dat, bx => checkExcl_eq g A bx dat
  | .wit dat, bx => checkWit_eq g A bx dat
  | .split j c0 c1 c2 c3, bx => by
    simp only [walk, C64Chk.walk]
    rw [walk_eq g A c0, walk_eq g A c1, walk_eq g A c2, walk_eq g A c3]

lemma pinROK_eq (g : Glob) (p : KCBall) (R : Q) : pinROK g p R = C64Chk.pinROK g (toC p) R := by
  unfold pinROK C64Chk.pinROK
  rw [expPiHi_eq, absHi_eq, cfg_toC]
  refine any_eq rfl fun eY => ?_
  simp only [blt_eq, SI.le_eq, SI.toInt_ofNat, loS_eq, toBall_qBall, npow, nmul, cdiv_eq]
  rfl

lemma T1B_eq (g : Glob) : toE (T1B g) = C64Chk.T1B g := toE_ellOf g.P _

lemma pinBall_eq (P : Nat) (p : Q × Q) : toC (pinBall P p) = C64Chk.pinBall P p := by
  simp [pinBall, C64Chk.pinBall, toC, toBall_qBall]

lemma mapM_ptT_eq (c : KNum.Cfg) (D : Nat) : ∀ (l : List KCBall),
    (l.mapM (ptT c D)).map (List.map toPt) = (l.map toC).mapM (C64Chk.ptT c.toC D)
  | [] => rfl
  | z :: l => by
    simp only [List.mapM_cons, List.map_cons]
    refine bind_sim (ptT_eq c D z) fun T => ?_
    refine bind_sim (mapM_ptT_eq c D l) fun Ts => ?_
    rfl

lemma map_zip3 (l1 : List KCBall) (l2 : List PtT) (l3 : List Q) :
    (l1.zip (l2.zip l3)).map toPin = (l1.map toC).zip ((l2.map toPt).zip l3) := by
  induction l1 generalizing l2 l3 with
  | nil => rfl
  | cons a l1 ih =>
    cases l2 with
    | nil => rfl
    | cons b l2 =>
      cases l3 with
      | nil => rfl
      | cons c l3 => simp [ih, toPin]

lemma map_pinBall (P : Nat) (pins : List (Q × Q)) : (pins.map (pinBall P)).map toC = pins.map (C64Chk.pinBall P) := by
  rw [List.map_map]
  exact List.map_congr_left fun p _ => pinBall_eq P p

lemma arcCtx_eq (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) :
    (arcCtx g s0 s1 sc pins Rs rX).map toAC = C64Chk.arcCtx g s0 s1 sc pins Rs rX := by
  unfold arcCtx C64Chk.arcCtx
  have hz := ellPt_eq ⟨g.P, g.n, g.k⟩ (T1B g) (dyB g.P sc g.ES)
  rw [T1B_eq, toBall_dyB, cfg_toC] at hz
  refine bind_sim hz fun zc => ?_
  refine bind_sim (toC_cSS1 _ zc) fun ss => ?_
  refine bind_sim (ptT_eq _ g.D zc) fun zT => ?_
  rw [rBound_eq, T1B_eq]
  refine bind_eq rfl fun r => ?_
  have hm := mapM_ptT_eq ⟨g.P, g.n, g.k⟩ g.D (pins.map (pinBall g.P))
  rw [map_pinBall] at hm
  refine map_sim hm fun pts => ?_
  simp only [toAC, map_zip3, map_pinBall, T1B_eq]
  rfl

lemma allPinROK_eq (g : Glob) : ∀ (l : List (Q × Q)) (Rs : List Q),
    ((l.map (pinBall g.P)).zip Rs).all (fun x => pinROK g x.1 x.2) =
      ((l.map (C64Chk.pinBall g.P)).zip Rs).all (fun x => C64Chk.pinROK g x.1 x.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: l, R :: Rs => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons]
    rw [allPinROK_eq g l Rs, pinROK_eq, pinBall_eq]

lemma hHead_eq (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) :
    hHead g s0 s1 sc pins Rs = C64Chk.hHead g s0 s1 sc pins Rs := by
  unfold hHead C64Chk.hHead
  rw [allPinROK_eq]
  simp only [nble, blt_eq, nbeq]

lemma checkH_eq (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : Tree) :
    checkH g s0 s1 sc pins Rs rX t = C64Chk.checkH g s0 s1 sc pins Rs rX t := by
  unfold checkH C64Chk.checkH
  rw [hHead_eq, any_sim (arcCtx_eq g s0 s1 sc pins Rs rX)
    (p' := fun A => C64Chk.walk g A t (pins.map fun _ => (0, 0, 0))) fun A => walk_eq g A t _]

/-- One leaf (or subtree) of an H arc, as in the leaf-level shards: the kernel checker computes exactly the
`C64Chk` value. -/
theorem arcWalk_eq (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (t : Tree)
    (bx : List (Nat × Nat × Nat)) :
    (arcCtx g s0 s1 sc pins Rs rX).any (fun A => walk g A t bx) =
      (C64Chk.arcCtx g s0 s1 sc pins Rs rX).any (fun A => C64Chk.walk g A t bx) :=
  any_sim (arcCtx_eq g s0 s1 sc pins Rs rX) fun A => walk_eq g A t bx

/-- Any test of the arc context that the kernel layer computes as a `C64Chk` test (e.g. a conjunction of leaf walks,
as in the leaf-group shards): the kernel value equals the `C64Chk` value. -/
theorem arcAny_eq (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat)
    (FK : ACtx → Bool) (F : C64Chk.ACtx → Bool) (h : ∀ A, FK A = F (toAC A)) :
    (arcCtx g s0 s1 sc pins Rs rX).any FK = (C64Chk.arcCtx g s0 s1 sc pins Rs rX).any F :=
  any_sim (arcCtx_eq g s0 s1 sc pins Rs rX) h

/-- A hoisted arc context: from `arcCtxK .. = some A0` (e.g. by `rfl` or `decide +kernel` with a literal `A0`),
`C64Chk.arcCtx .. = some (toAC A0)`. -/
theorem arcCtx_some (g : Glob) (s0 s1 sc : Nat) (pins : List (Q × Q)) (Rs : List Q) (rX : Nat) (A0 : ACtx)
    (h : arcCtx g s0 s1 sc pins Rs rX = some A0) : C64Chk.arcCtx g s0 s1 sc pins Rs rX = some (toAC A0) := by
  rw [← arcCtx_eq, h]
  rfl

/-- The kernel checker of an arc computes exactly `C64Chk.checkArc`. -/
theorem checkArc_eq (g : Glob) (a : Arc) : checkArc g a = C64Chk.checkArc g a := by
  cases a with
  | E s0 s1 ur ui =>
    simp only [checkArc, C64Chk.checkArc, blt_eq]
    rw [checkE_eq, T1B_eq, toC_intC]
  | H s0 s1 sc pins Rs rX t => exact checkH_eq g s0 s1 sc pins Rs rX t

/-- The kernel checker of the global conditions computes exactly `C64Chk.checkGlob`. -/
theorem checkGlob_eq (g : Glob) : checkGlob g = C64Chk.checkGlob g := by
  unfold checkGlob C64Chk.checkGlob
  rw [windOdd_eq, T1B_eq]

end C64KChk
