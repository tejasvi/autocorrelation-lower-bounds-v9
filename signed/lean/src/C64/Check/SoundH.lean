import C64.Check.SoundWitL

/-!
# Soundness of the checker, part 8: the leaf tree, type H arcs, `checkArc`
-/

namespace C64Chk

open MeasureTheory Ival Ival.Ball C64Num Real

variable {P : ℕ}

/-! ### The leaf tree -/

theorem pqL_split {f : ℂ → ℂ} : ∀ (j : ℕ) (ps : List ℂ) (pins : List (CBall × PtT × Q)) (bx : List (ℕ × ℕ × ℕ)),
    (∀ pb ∈ pins, 0 ≤ pb.2.2.val) → j < bx.length → ps.length = bx.length → pins.length = bx.length →
    (∀ x ∈ pqL ps pins bx, x.2.mem (f x.1)) →
    ∃ n < 4, ∀ x ∈ pqL ps pins (bx.set j (kid (bx.getD j (0, 0, 0)) n)), x.2.mem (f x.1)
  | 0, p :: ps, pb :: pins, b :: bx, hR, _, _, _, hmem => by
    have h0 := hmem (p, boxR pb.2.2 b.1 b.2.1 b.2.2) (by simp [pqL])
    obtain ⟨d, i, k⟩ := b
    obtain ⟨n, hn, hn'⟩ := boxR_split pb.2.2 (hR pb (by simp)) d i k h0
    refine ⟨n, hn, fun x hx => ?_⟩
    simp only [List.set_cons_zero, List.getD_cons_zero, pqL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hn'
    · exact hmem x (by simp [pqL, hx])
  | j + 1, p :: ps, pb :: pins, b :: bx, hR, hj, h1, h2, hmem => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff] at hj h1 h2
    obtain ⟨n, hn, hn'⟩ := pqL_split j ps pins bx (fun q hq => hR q (by simp [hq])) hj h1 h2
      (fun x hx => hmem x (by simp [pqL, hx]))
    refine ⟨n, hn, fun x hx => ?_⟩
    simp only [List.set_cons_succ, List.getD_cons_succ, pqL, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hmem _ (by simp [pqL])
    · exact hn' x hx
  | _, [], _, _, _, hj, h1, _, _ => by simp at h1; simp [← h1] at hj
  | _, _ :: _, [], _, _, hj, _, h2, _ => by simp at h2; simp [← h2] at hj
  | _, _ :: _, _ :: _, [], _, hj, _, _, _ => by simp at hj

theorem walk_ok {g : Glob} (hg : GlobOK g) {A : ACtx} {zc : ℂ} {ps : List ℂ} (hA : ACtxOK g A zc ps)
    (hR : ∀ pb ∈ A.pins, 0 ≤ pb.2.2.val) :
    ∀ (t : Tree) (bx : List (ℕ × ℕ × ℕ)), bx.length = ps.length → walk g A t bx = true →
    ∀ μ : Measure ℝ, (∀ x ∈ pqL ps A.pins bx, x.2.mem (C64.hat μ x.1)) →
    ∃ pq : List (ℂ × C64.Box), (∀ x ∈ pq, x.2.mem (C64.hat μ x.1)) ∧
      C64.LeafSettledL g.tau.val zc ((A.r : ℝ) / 2 ^ g.P) pq
  | .excl dat, bx, hbx, h, μ, hmem => ⟨_, hmem, checkExcl_ok hg hA hbx h⟩
  | .wit dat, bx, hbx, h, μ, hmem => ⟨_, hmem, checkWit_ok hg hA hbx h⟩
  | .split j c0 c1 c2 c3, bx, hbx, h, μ, hmem => by
    unfold walk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hj, h0⟩, h1⟩, h2⟩, h3⟩ := h
    have hlen : A.pins.length = ps.length := (List.Forall₂.length_eq hA.hpins).symm
    obtain ⟨n, hn, hn'⟩ := pqL_split j ps A.pins bx hR hj hbx.symm (by rw [hlen, hbx]) hmem
    have hl : ∀ m, (bx.set j (kid (bx.getD j (0, 0, 0)) m)).length = ps.length := fun m => by
      rw [List.length_set, hbx]
    interval_cases n
    · exact walk_ok hg hA hR c0 _ (hl 0) h0 μ hn'
    · exact walk_ok hg hA hR c1 _ (hl 1) h1 μ hn'
    · exact walk_ok hg hA hR c2 _ (hl 2) h2 μ hn'
    · exact walk_ok hg hA hR c3 _ (hl 3) h3 μ hn'

/-! ### Type H arcs -/

theorem pinROK_ok {g : Glob} (hg : GlobOK g) {pb : CBall} {R : Q} {p : ℂ} (hp : memC g.P p pb)
    (h : pinROK g pb R = true) : 0 < R.d ∧ g.tau.val * Real.exp (π * |p.im|) ≤ R.val := by
  unfold pinROK at h
  simp only [Option.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨eY, heY, hd, hle⟩ := h
  refine ⟨hd, ?_⟩
  have hP := two_pow_pos' g.P
  have he : Real.exp (π * |p.im|) ≤ (eY : ℝ) / 2 ^ g.P := exp_le_expPiHi heY (abs_le_absHi hp.2)
  have htd : 0 < g.tau.d := by have := lt_trans hg.tn hg.tlt; omega
  have hτU : g.tau.val ≤ (Ball.cdiv (g.tau.n.toNat * 2 ^ g.P) g.tau.d : ℝ) / 2 ^ g.P := by
    rw [tau_eq hg]
    have h' := cdiv_spec (g.tau.n.toNat * 2 ^ g.P) g.tau.d htd
    push_cast at h'
    rw [le_div_iff₀ hP]
    calc (g.tau.n.toNat : ℝ) / g.tau.d * 2 ^ g.P = (g.tau.n.toNat : ℝ) * 2 ^ g.P / g.tau.d := by ring
      _ ≤ _ := h'
  have hm := mulU_le (tau_pos hg).le (Real.exp_pos _).le hτU he
  have hRlo := (mem_iff_lo_hi.1 (mem_Qball (P := g.P) hd)).1
  have : (mulU g.P (Ball.cdiv (g.tau.n.toNat * 2 ^ g.P) g.tau.d) eY : ℝ) / 2 ^ g.P ≤
      ((R.ball g.P).lo : ℝ) / 2 ^ g.P :=
    div_le_div_of_nonneg_right (by exact_mod_cast hle) hP.le
  linarith

theorem mapM_some {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
    List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl'', rfl⟩ := h
    exact List.Forall₂.cons hb (mapM_some hl'')

theorem forall2_snd {α β : Type} {R : α → β → Prop} {Q' : β → Prop} (hQ : ∀ a b, R a b → Q' b) :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, Q' b
  | _, _, .nil => by simp
  | _, _, .cons h hs => by
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hQ _ _ h
    · exact forall2_snd hQ hs b hb

/-- The pinned points of an H arc. -/
noncomputable def pinVal (p : Q × Q) : ℂ := ⟨p.1.val, p.2.val⟩

theorem pins_forall2 {g : Glob} (hg : GlobOK g) : ∀ (pins : List (Q × Q)) (Rs : List Q) (pts : List PtT),
    pins.length = Rs.length → (∀ x ∈ pins, 0 < x.1.d ∧ 0 < x.2.d) →
    (∀ x ∈ (pins.map (pinBall g.P)).zip Rs, pinROK g x.1 x.2 = true) →
    List.Forall₂ (fun a b => ptT g.cfg g.D a = some b) (pins.map (pinBall g.P)) pts →
    List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧
      0 < pb.2.2.d ∧ g.tau.val * Real.exp (π * |p.im|) ≤ pb.2.2.val)
      (pins.map pinVal) ((pins.map (pinBall g.P)).zip (pts.zip Rs))
  | [], Rs, pts, _, _, _, hF => by
    cases hF; simp
  | p :: pins, R :: Rs, pt :: pts, hlen, hden, hpinR, hF => by
    cases hF with
    | cons hpt hrest =>
      simp only [List.map_cons, List.zip_cons_cons]
      have hpd := hden p (by simp)
      have hpd' : memC g.P (pinVal p) (pinBall g.P p) := ⟨mem_Qball hpd.1, mem_Qball hpd.2⟩
      obtain ⟨hRd, hRb⟩ := pinROK_ok hg hpd' (hpinR (pinBall g.P p, R) (by simp))
      exact List.Forall₂.cons ⟨hpd', ptT_ok hpd' hg.D1 hg.hD hpt, hRd, hRb⟩
        (pins_forall2 hg pins Rs pts (by simpa using hlen) (fun q hq => hden q (by simp [hq]))
          (fun x hx => hpinR x (by simp only [List.map_cons, List.zip_cons_cons, List.mem_cons]; exact Or.inr hx))
          hrest)
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _ :: _, [], _, _, _, hF => by cases hF

theorem checkH_ok {g : Glob} (hg : GlobOK g) {s0 s1 sc : ℕ} {pins : List (Q × Q)} {Rs : List Q} {rX : ℕ}
    {t : Tree} (h : checkH g s0 s1 sc pins Rs rX t = true) :
    C64.ArcSettled g.tau.val g.c.val g.a.val g.b.val ((s0 : ℝ) / 2 ^ g.ES) ((s1 : ℝ) / 2 ^ g.ES) := by
  unfold checkH at h
  simp only [Bool.and_eq_true, Option.any_eq_true] at h
  obtain ⟨hhead, A, hAc, hw⟩ := h
  unfold hHead at hhead
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hhead
  obtain ⟨⟨⟨⟨⟨h0c, hc1⟩, h01⟩, hlen⟩, hden⟩, hpinR⟩ := hhead
  unfold arcCtx at hAc
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hAc
  obtain ⟨zcB, hzc, ⟨Sc, S1c⟩, hss, zT, hzT, r, hr, pts, hpts, rfl⟩ := hAc
  have hP := two_pow_pos' g.P
  have hE1 := T1_ok hg
  set zc := C64.ellipse (g.c.val : ℂ) g.a.val g.b.val ((sc : ℝ) / 2 ^ g.ES)
  have hzcm : memC g.P zc zcB := by
    have := mem_dyB (P := g.P) (sc : ℤ) (show g.ES ≤ g.P by have := hg.hE; omega)
    push_cast at this
    exact memC_ellPt hE1 this hzc
  obtain ⟨-, hSc, hS1c⟩ := memC_cSS1 hzcm hss
  have hzTok := ptT_ok hzcm hg.D1 hg.hD hzT
  set ps := pins.map pinVal
  -- the semantic arc context, with the radii bounds
  have hF := mapM_some hpts
  have hpinsF' := pins_forall2 hg pins Rs pts hlen hden hpinR hF
  have hpinsF : List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧
      0 < pb.2.2.d) ps ((pins.map (pinBall g.P)).zip (pts.zip Rs)) :=
    hpinsF'.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  set A : ACtx := ⟨T1B g, s0, s1, sc, zcB, Sc, S1c, zT, r, (pins.map (pinBall g.P)).zip (pts.zip Rs)⟩
  have hA : ACtxOK g A zc ps := ⟨hzcm, hSc, hS1c, hzTok, hpinsF⟩
  have hτ0 := (tau_pos hg).le
  have hR : ∀ pb ∈ A.pins, 0 ≤ pb.2.2.val :=
    forall2_snd (fun _ _ h => le_trans (mul_nonneg hτ0 (Real.exp_pos _).le) h.2.2.2) hpinsF'
  -- every measure of the class has its pinned values in the root boxes
  have hroot : ∀ μ : Measure ℝ, C64.ClassA g.tau.val μ →
      ∀ x ∈ pqL ps A.pins (pins.map fun _ => ((0 : ℕ), (0 : ℕ), (0 : ℕ))), x.2.mem (C64.hat μ x.1) := by
    intro μ hμ
    have key : ∀ (l1 : List ℂ) (l2 : List (CBall × PtT × Q)) (l0 : List (Q × Q)),
        List.Forall₂ (fun p (pb : CBall × PtT × Q) => memC g.P p pb.1 ∧ PtOK g.P g.D p pb.2.1 ∧
          0 < pb.2.2.d ∧ g.tau.val * Real.exp (π * |p.im|) ≤ pb.2.2.val) l1 l2 →
        ∀ x ∈ pqL l1 l2 (l0.map fun _ => ((0 : ℕ), (0 : ℕ), (0 : ℕ))), x.2.mem (C64.hat μ x.1) := by
      intro l1 l2 l0 hF2
      induction hF2 generalizing l0 with
      | nil => intro x hx; simp [pqL] at hx
      | @cons p pb l1 l2 hab _ ih =>
        cases l0 with
        | nil => intro x hx; simp [pqL] at hx
        | cons q l0 =>
          intro x hx
          simp only [List.map_cons, pqL, List.mem_cons] at hx
          rcases hx with rfl | hx
          · obtain ⟨hre, him⟩ := C64.pinned_bound hτ0 hμ hab.2.2.2
            exact boxR_root pb.2.2 hre him
          · exact ih l0 x hx
    exact key ps A.pins pins hpinsF'
  have htd : 0 < g.tau.d := by have := lt_trans hg.tn hg.tlt; omega
  have hloc := rBound_ok hg h0c hc1 htd hzcm hSc hS1c hr
  rw [← tau_eq hg] at hloc
  refine C64.settled_HL hloc (fun μ hμ => ?_)
  exact walk_ok hg hA hR t _ (by simp [ps]) hw μ (hroot μ hμ)

theorem checkArc_ok {g : Glob} (hg : GlobOK g) (a : Arc) (h : checkArc g a = true) :
    C64.ArcSettled g.tau.val g.c.val g.a.val g.b.val ((a.s0 : ℝ) / 2 ^ g.ES) ((a.s1 : ℝ) / 2 ^ g.ES) := by
  cases a with
  | E s0 s1 ur ui => exact checkArcE_ok hg h
  | H s0 s1 sc pins Rs rX t => exact checkH_ok hg h

end C64Chk
