import Mathlib
import C64Core.Check
import C64K.KChk
import C64K.KNumSim

/-!
# Simulation: the kernel checker computes exactly what `C64Chk` computes

Every ball of `C64KChk` maps to the corresponding ball of `C64Chk` under `KBall.toBall` / `KCBall.toC` (signed
pairs under `SI.toInt`), so that `checkArcK g a = checkArc g a` and `checkGlobK g = checkGlob g`
(`C64KChk.checkArc_eq`, `C64KChk.checkGlob_eq`): every soundness lemma about `C64Chk` applies to the kernel checker
by rewriting.
-/

namespace C64KChk

open KIval KIval.KBall KNum KNum.KCBall C64Chk

/-! ## Generic transport lemmas -/

lemma bind_sim {α β α' β' : Type} {o : Option α} {o' : Option α'} {f : α → α'} (ho : o.map f = o')
    {g : α → Option β} {g' : α' → Option β'} {h : β → β'} (hg : ∀ a, (g a).map h = g' (f a)) :
    (o.bind g).map h = o'.bind g' := by
  subst ho; cases o <;> simp [hg]

lemma bind_sim' {α β α' : Type} {o : Option α} {o' : Option α'} {f : α → α'} (ho : o.map f = o')
    {g : α → Option β} {g' : α' → Option β} (hg : ∀ a, g a = g' (f a)) :
    o.bind g = o'.bind g' := by
  subst ho; cases o <;> simp [hg]

lemma map_sim {α β α' β' : Type} {o : Option α} {o' : Option α'} {f : α → α'} (ho : o.map f = o')
    {g : α → β} {g' : α' → β'} {h : β → β'} (hg : ∀ a, h (g a) = g' (f a)) :
    (o.map g).map h = o'.map g' := by
  subst ho; cases o <;> simp [hg]

lemma map_sim' {α β α' : Type} {o : Option α} {o' : Option α'} {f : α → α'} (ho : o.map f = o')
    {g : α → β} {g' : α' → β} (hg : ∀ a, g a = g' (f a)) :
    o.map g = o'.map g' := by
  subst ho; cases o <;> simp [hg]

lemma bind_eq {α β β' : Type} {o o' : Option α} (ho : o = o') {g : α → Option β} {g' : α → Option β'}
    {h : β → β'} (hg : ∀ a, (g a).map h = g' a) : (o.bind g).map h = o'.bind g' := by
  subst ho; cases o <;> simp [hg]

lemma bind_eq' {α β : Type} {o o' : Option α} (ho : o = o') {g g' : α → Option β} (hg : ∀ a, g a = g' a) :
    o.bind g = o'.bind g' := by
  subst ho; cases o <;> simp [hg]

lemma map_eq' {α β β' : Type} {o o' : Option α} (ho : o = o') {g : α → β} {g' : α → β'} {h : β → β'}
    (hg : ∀ a, h (g a) = g' a) : (o.map g).map h = o'.map g' := by
  subst ho; cases o <;> simp [hg]

lemma any_eq {α : Type} {o o' : Option α} (ho : o = o') {p p' : α → Bool} (hp : ∀ a, p a = p' a) :
    o.any p = o'.any p' := by
  subst ho; cases o <;> simp [hp]

lemma any_sim {α α' : Type} {o : Option α} {o' : Option α'} {f : α → α'} (ho : o.map f = o')
    {p : α → Bool} {p' : α' → Bool} (hp : ∀ a, p a = p' (f a)) : o.any p = o'.any p' := by
  subst ho; cases o <;> simp [hp]

/-! ## Signed integers -/

/-- The integer `(-1)^s m`. -/
def SI.toInt (a : SI) : Int := sval a.s a.m

@[simp] lemma SI.toInt_ofNat (n : Nat) : SI.toInt (SI.ofNat n) = n := rfl

@[simp] lemma SI.toInt_add (a b : SI) : SI.toInt (SI.add a b) = SI.toInt a + SI.toInt b :=
  sval_sadd a.s a.m b.s b.m 0

@[simp] lemma SI.toInt_sub (a b : SI) : SI.toInt (SI.sub a b) = SI.toInt a - SI.toInt b := by
  show sval (sadd a.s a.m (cond b.s false true) b.m 0).s (sadd a.s a.m (cond b.s false true) b.m 0).m = _
  rw [sval_sadd, sval_not]; rfl

@[simp] lemma SI.le_eq (a b : SI) : SI.le a b = decide (SI.toInt a ≤ SI.toInt b) := sle_eq _ _ _ _

@[simp] lemma SI.lt_eq (a b : SI) : SI.lt a b = decide (SI.toInt a < SI.toInt b) := by
  unfold SI.lt
  rw [sle_eq]
  by_cases h : sval b.s b.m ≤ sval a.s a.m
  · simp [h, SI.toInt, not_lt.mpr h]
  · simp [h, SI.toInt, lt_of_not_ge h]

@[simp] lemma SI.toNat_eq (a : SI) : SI.toNat a = (SI.toInt a).toNat := by
  unfold SI.toNat SI.toInt; cases a.s <;> simp [sval]

@[simp] lemma SI.nonneg_eq (a : SI) : SI.nonneg a = decide (0 ≤ SI.toInt a) := by
  unfold SI.nonneg SI.toInt; cases a.s <;> simp [sval]

@[simp] lemma SI.toInt_mul (a b : SI) : SI.toInt (SI.mul a b) = SI.toInt a * SI.toInt b := by
  unfold SI.mul SI.toInt; rw [sval_xor]; simp

@[simp] lemma sval_negI (n : Int) : sval (negI n) n.natAbs = n := by
  cases n <;> simp [negI, sval] <;> omega

@[simp] lemma SI.toInt_sI (n : Int) : SI.toInt (sI n) = n := sval_negI n

lemma loS_eq (a : KBall) : SI.toInt (loS a) = (toBall a).lo := by
  show sval (sadd a.s a.m true a.r 0).s (sadd a.s a.m true a.r 0).m = _
  rw [sval_sadd]; simp [Ival.Ball.lo, sval]; ring

lemma hiS_eq (a : KBall) : SI.toInt (hiS a) = (toBall a).hi := by
  show sval (sadd a.s a.m false a.r 0).s (sadd a.s a.m false a.r 0).m = _
  rw [sval_sadd]; simp [Ival.Ball.hi, sval]

lemma hiNat_eq (a : KBall) : hiNat a = (toBall a).hi.toNat := by
  unfold hiNat; rw [SI.toNat_eq, hiS_eq]

/-! ## Balls of exact data -/

lemma toBall_qBall (P : Nat) (q : Q) : toBall (qBall P q) = Q.ball P q := by
  unfold qBall Q.ball; rw [toBall_ofRat, sval_negI]

lemma toBall_dyB (P n e : Nat) : toBall (dyB P n e) = C64Chk.dyB P (n : Int) e := by
  unfold dyB C64Chk.dyB toBall; simp [sval]

lemma toC_intC (P : Nat) (x : Int × Int) : toC (intC P x) = C64Chk.intC P x := by
  unfold intC C64Chk.intC toC; simp only [toBall_ofInt, sval_negI]

lemma piHi_eq (P : Nat) : piHi P = C64Chk.piHi P := by
  unfold piHi C64Chk.piHi; rw [hiNat_eq, toBall_piB]

lemma mulU_eq (P x y : Nat) : mulU P x y = C64Chk.mulU P x y := rfl

lemma expPiHi_eq (c : KNum.Cfg) (Y : Nat) : expPiHi c Y = C64Chk.expPiHi c.toC Y := by
  unfold expPiHi C64Chk.expPiHi
  have h := toBall_expB c.P c.n (KBall.mul c.P (piB c.P) ⟨false, Y, 0⟩)
  rw [toBall_mul, toBall_piB] at h
  rw [show (⟨(Y : Int), 0⟩ : Ival.Ball) = toBall ⟨false, Y, 0⟩ from rfl]
  simp only [KNum.Cfg.toC]
  rw [← h]
  cases expB c.P c.n (KBall.mul c.P (piB c.P) ⟨false, Y, 0⟩) <;> simp [hiNat_eq]

lemma reConjLo_eq (P : Nat) (u w : KCBall) : SI.toInt (reConjLo P u w) = C64Chk.reConjLo P (toC u) (toC w) := by
  unfold reConjLo C64Chk.reConjLo
  rw [loS_eq, ← toC_conj, ← toC_mul]; rfl

lemma reConjHi_eq (P : Nat) (u w : KCBall) : SI.toInt (reConjHi P u w) = C64Chk.reConjHi P (toC u) (toC w) := by
  unfold reConjHi C64Chk.reConjHi
  rw [hiS_eq, ← toC_conj, ← toC_mul]; rfl

/-! ## Ellipses -/

def toE (E : EllB) : C64Chk.EllB := ⟨toBall E.cr, toBall E.ci, toBall E.a, toBall E.b⟩

lemma toE_ellOf (P : Nat) (e : Q × Q × Q × Q) : toE (ellOf P e) = C64Chk.ellOf P e := by
  simp [toE, ellOf, C64Chk.ellOf, toBall_qBall]

lemma ellPt_eq (c : KNum.Cfg) (E : EllB) (U : KBall) :
    (ellPt c E U).map toC = C64Chk.ellPt c.toC (toE E) (toBall U) := by
  unfold ellPt C64Chk.ellPt
  exact map_sim (toBall_cosSinTurn c.P c.n c.k U) fun cs => by
    simp [toC, toE, toBall_add, toBall_mul, KNum.Cfg.toC]

lemma ellSp_eq (c : KNum.Cfg) (E : EllB) (U : KBall) : ellSp c E U = C64Chk.ellSp c.toC (toE E) (toBall U) := by
  unfold ellSp C64Chk.ellSp
  exact map_sim' (toBall_cosSinTurnC c.P c.n c.k U) fun cs => by
    simp [toE, absHi_eq, sqrtHi, C64Num.sqrtHi, KNum.Cfg.toC]

lemma toBall_midB (P n0 n1 e : Nat) : toBall (midB P n0 n1 e) = C64Chk.midB P n0 n1 e := by
  unfold midB C64Chk.midB; rw [toBall_dyB]; simp

lemma toBall_pieceB (P n0 n1 e : Nat) : toBall (pieceB P n0 n1 e) = C64Chk.pieceB P n0 n1 e := by
  unfold pieceB C64Chk.pieceB toBall; simp [sval]

lemma ellRad_eq (c : KNum.Cfg) (E : EllB) (n0 n1 e : Nat) :
    ellRad c E n0 n1 e = C64Chk.ellRad c.toC (toE E) n0 n1 e := by
  unfold ellRad C64Chk.ellRad
  rw [ellSp_eq, toBall_pieceB]
  simp [piHi_eq, KNum.Cfg.toC]

lemma lsLoc_eq (c : KNum.Cfg) (z s1 : KCBall) (rho : Nat) :
    lsLoc c z s1 rho = C64Chk.lsLoc c.toC (toC z) (toC s1) rho := by
  unfold lsLoc C64Chk.lsLoc
  rw [expPiHi_eq]
  simp [absHi_eq, normHi_eq, piHi_eq, KNum.Cfg.toC]

/-! ## Bounds in `t` -/

def toSt (st : List (KCBall × KCBall)) : List (C64Num.CBall × C64Num.CBall) := st.map (Prod.map toC toC)

def toPt (T : PtT) : C64Chk.PtT := ⟨toSt T.st, toC T.w, T.mz⟩

def toTm (T : TermS) : C64Chk.TermS := ⟨toC T.W, toC T.w, toSt T.st, T.m2⟩

lemma sqChain_eq (P : Nat) : ∀ (j : Nat) (x : KCBall × KCBall) (acc : List (KCBall × KCBall)),
    toSt (sqChain P j x acc) = C64Chk.sqChain P j (Prod.map toC toC x) (toSt acc)
  | 0, x, acc => by simp [sqChain, C64Chk.sqChain, toSt]
  | j + 1, x, acc => by
    simp only [sqChain, C64Chk.sqChain]
    rw [sqChain_eq P j]
    simp [toSt, toC_mul]

lemma piSqHi_eq (P : Nat) : piSqHi P = C64Chk.piSqHi P := by
  unfold piSqHi C64Chk.piSqHi; rw [piHi_eq]; rfl

lemma ptT_eq (c : KNum.Cfg) (D : Nat) (z : KCBall) : (ptT c D z).map toPt = C64Chk.ptT c.toC D (toC z) := by
  unfold ptT C64Chk.ptT
  have hh : toBall (dyB c.P 1 (Nat.add D 1)) = C64Chk.dyB c.toC.P 1 (D + 1) := by
    rw [toBall_dyB]; rfl
  have h1 := toC_ckt c (dyB c.P 1 (Nat.add D 1)) z
  rw [hh] at h1
  have h2 := toC_ckt c (KBall.neg (dyB c.P 1 (Nat.add D 1))) z
  rw [toBall_neg, hh] at h2
  refine bind_sim h1 fun kp => ?_
  refine bind_sim h2 fun km => ?_
  rw [expPiHi_eq]
  simp only [absHi_eq, toC_im, cdiv_eq]
  cases C64Chk.expPiHi c.toC (Ival.Ball.cdiv (Ival.Ball.absHi (toBall z.im)) 16) with
  | none => rfl
  | some f0 =>
    simp only [Option.map_some, toPt, Option.some.injEq]
    rw [sqChain_eq]
    simp [toC, toSt, toBall_mulInt, toBall_mul, toBall_piB, toBall_neg, piSqHi_eq, normHi_eq, KNum.Cfg.toC,
      C64Chk.mulU, mulU]

lemma termOf_eq (cf : KCBall) (T : PtT) : toTm (termOf cf T) = C64Chk.termOf (toC cf) (toPt T) := rfl

lemma reMul_eq (P : Nat) (a b : KCBall) : toBall (reMul P a b) = C64Chk.reMul P (toC a) (toC b) := by
  simp [reMul, C64Chk.reMul, toBall_sub, toBall_mul]

def toS3 (r : KBall × KBall × Nat) : Ival.Ball × Ival.Ball × Nat := (toBall r.1, toBall r.2.1, r.2.2)

lemma sumTerms_eq (P : Nat) : ∀ ts : List TermS, toS3 (sumTerms P ts) = C64Chk.sumTerms P (ts.map toTm)
  | [] => rfl
  | T :: ts => by
    simp only [sumTerms, C64Chk.sumTerms, List.map_cons]
    rw [← sumTerms_eq P ts]
    simp [toS3, toBall_add, reMul_eq, absHi_eq, toTm, mulU_eq]

lemma cellOK_eq (P : Nat) (ts : List TermS) (e : Nat) (target : SI) :
    cellOK P ts e target = C64Chk.cellOK P (ts.map toTm) e (SI.toInt target) := by
  unfold cellOK C64Chk.cellOK
  rw [← sumTerms_eq]
  simp only [toS3, SI.lt_eq, SI.toInt_add, hiS_eq, SI.toInt_ofNat, absHi_eq, nble, cdiv_eq, npow, nadd, nmul]
  cases h : decide (5 ≤ e) <;> simp_all [add_assoc]

lemma stepT_eq (P : Nat) (down : Bool) (T : TermS) : toTm (stepT P down T) = C64Chk.stepT P down (toTm T) := by
  unfold stepT C64Chk.stepT
  cases h : T.st with
  | nil => simp [toTm, toSt, h]
  | cons x rest =>
    obtain ⟨kp, km⟩ := x
    simp only [toTm, toSt, h, List.map_cons, Prod.map]
    cases down <;> simp [toC_mul]

lemma map_stepT (P : Nat) (d : Bool) (ts : List TermS) :
    (ts.map (stepT P d)).map toTm = (ts.map toTm).map (C64Chk.stepT P d) := by
  simp only [List.map_map]
  exact List.map_congr_left fun T _ => stepT_eq P d T

lemma cells_eq (P : Nat) (target : SI) : ∀ (fuel skip e : Nat) (ts : List TermS),
    cells P target fuel skip e ts = C64Chk.cells P (SI.toInt target) fuel skip e (ts.map toTm)
  | 0, _, _, _ => rfl
  | fuel + 1, skip, e, ts => by
    simp only [cells, C64Chk.cells]
    rw [cells_eq P target fuel, cells_eq P target fuel, cellOK_eq, map_stepT, map_stepT]
    simp only [nbeq, nsub, nadd, cond_and_false]
    cases skip <;> simp

lemma tbound_eq (P D : Nat) (ts : List TermS) (target : SI) :
    tbound P D ts target = C64Chk.tbound P D (ts.map toTm) (SI.toInt target) := by
  unfold tbound C64Chk.tbound; rw [cells_eq]

/-! ## Pieces and type E arcs -/

def toPD (pd : PieceD) : C64Chk.PieceD := ⟨toC pd.z, pd.rho, toC pd.sz, toC pd.s1, pd.ls, pd.eY⟩

lemma pieceD_eq (c : KNum.Cfg) (E : EllB) (n0 n1 e : Nat) :
    (pieceD c E n0 n1 e).map toPD = C64Chk.pieceD c.toC (toE E) n0 n1 e := by
  unfold pieceD C64Chk.pieceD
  have hz := ellPt_eq c E (midB c.P n0 n1 e)
  rw [toBall_midB] at hz
  refine bind_sim hz fun z => ?_
  refine bind_eq (ellRad_eq c E n0 n1 e) fun rho => ?_
  refine bind_sim (toC_cSS1 c z) fun ss => ?_
  refine bind_eq (lsLoc_eq c z ss.2 rho) fun ls => ?_
  refine map_eq' ?_ fun eY => rfl
  rw [expPiHi_eq, absHi_eq]
  rfl

lemma aLow_eq (P : Nat) (u : KCBall) (pd : PieceD) : SI.toInt (aLow P u pd) = C64Chk.aLow P (toC u) (toPD pd) := by
  unfold aLow C64Chk.aLow
  simp [reConjLo_eq, normHi_eq, mulU_eq, toPD]

lemma dPof_eq (P : Nat) (u : KCBall) (pd : PieceD) : dPof P u pd = C64Chk.dPof P (toC u) (toPD pd) := by
  unfold dPof C64Chk.dPof
  simp [normHi_eq, mulU_eq, piHi_eq, toPD]

lemma tgt_eq (tn td : Nat) (a : SI) (dP : Nat) : SI.toInt (tgt tn td a dP) = C64Chk.tgt tn td (SI.toInt a) dP := by
  unfold tgt C64Chk.tgt
  simp

lemma ePieceOK_eq (g : Glob) (u : KCBall) (pd : PieceD) (T : PtT) :
    ePieceOK g u pd T = C64Chk.ePieceOK g (toC u) (toPD pd) (toPt T) := by
  unfold ePieceOK C64Chk.ePieceOK
  rw [tbound_eq, SI.lt_eq, tgt_eq, aLow_eq, dPof_eq]
  simp [termOf_eq, toC_conj]

lemma checkEPiece_eq (g : Glob) (T1 : EllB) (u : KCBall) (n0 n1 e : Nat) :
    checkEPiece g T1 u n0 n1 e = C64Chk.checkEPiece g (toE T1) (toC u) n0 n1 e := by
  unfold checkEPiece C64Chk.checkEPiece
  exact any_sim (pieceD_eq _ T1 n0 n1 e) fun pd => any_sim (ptT_eq _ g.D pd.z) fun T => ePieceOK_eq g u pd T

lemma checkE_eq (g : Glob) (T1 : EllB) (u : KCBall) : ∀ (fuel n0 n1 e : Nat),
    checkE g T1 u fuel n0 n1 e = C64Chk.checkE g (toE T1) (toC u) fuel n0 n1 e
  | 0, n0, n1, e => checkEPiece_eq g T1 u n0 n1 e
  | fuel + 1, n0, n1, e => by
    simp only [checkE, C64Chk.checkE, nmul, nadd]
    rw [checkEPiece_eq, checkE_eq g T1 u fuel, checkE_eq g T1 u fuel]

/-! ## The crossing radius -/

lemma nmax_eq (a b : Nat) : nmax a b = max a b := by
  unfold nmax
  by_cases h : a ≤ b <;> simp [h, max_def]

lemma dOf_eq (P ES sp s0 s1 sc : Nat) : dOf P ES sp s0 s1 sc = C64Chk.dOf P ES sp s0 s1 sc := by
  unfold dOf C64Chk.dOf
  simp [piHi_eq, nmax_eq]

lemma mSOf_eq (P : Nat) (Sc : KCBall) (d L : Nat) : SI.toInt (mSOf P Sc d L) = C64Chk.mSOf P (toC Sc) d L := by
  unfold mSOf C64Chk.mSOf
  simp [normLo_eq, mulU_eq]

lemma rOf_eq (P tn td d L eY : Nat) (mS : SI) : rOf P tn td d L eY mS = C64Chk.rOf P tn td d L eY (SI.toInt mS) := by
  unfold rOf C64Chk.rOf
  simp [piHi_eq, mulU_eq]

/-! ## Boxes -/

def toB4 (B : Box4) : C64Chk.Box4 := (toBall B.1, toBall B.2.1, toBall B.2.2.1, toBall B.2.2.2)

lemma boxNum_eq (R : Q) (a b : Nat) : SI.toInt (boxNum R a b) = R.n * ((a : Int) - b) := by
  unfold boxNum
  rw [SI.toInt_mul, SI.toInt_sI]
  congr 1
  by_cases h : b ≤ a
  · simp [h, SI.toInt, sval]
  · simp [h, SI.toInt, sval]; omega

lemma toBall_boxEnd (P : Nat) (R : Q) (a b : Nat) :
    toBall (boxEnd P R a b) = Ival.Ball.ofRat P (R.n * ((a : Int) - b)) (R.d * b) := by
  unfold boxEnd
  rw [toBall_ofRat]
  have := boxNum_eq R a b
  unfold SI.toInt at this
  rw [this]; rfl

lemma boxB_eq (P : Nat) (R : Q) (d i k : Nat) : toB4 (boxB P R d i k) = C64Chk.boxB P R d i k := by
  simp only [toB4, boxB, C64Chk.boxB, toBall_boxEnd, nmul, npow, nadd]
  push_cast
  ring_nf

lemma toBall_cond (c : Bool) (x y : KBall) : toBall (cond c x y) = if c then toBall x else toBall y := by
  cases c <;> rfl

lemma boxLo_eq (y : Int × Int) (B : Box4) : SI.toInt (boxLo y B) = C64Chk.boxLo y (toB4 B) := by
  unfold boxLo C64Chk.boxLo
  rw [loS_eq]
  simp [toBall_add, toBall_mulInt, toB4, apply_ite toBall]

lemma boxHi_eq (y : Int × Int) (B : Box4) : SI.toInt (boxHi y B) = C64Chk.boxHi y (toB4 B) := by
  unfold boxHi C64Chk.boxHi
  rw [hiS_eq]
  simp [toBall_add, toBall_mulInt, toB4, apply_ite toBall]

lemma inBox_eq (w : KCBall) (B : Box4) : inBox w B = C64Chk.inBox (toC w) (toB4 B) := by
  unfold inBox C64Chk.inBox
  simp only [SI.le_eq, hiS_eq, loS_eq, toB4, toC_re, toC_im]
  rfl

end C64KChk
