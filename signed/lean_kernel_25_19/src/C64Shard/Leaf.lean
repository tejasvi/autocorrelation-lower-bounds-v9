import C64Shard.Shard

/-!
# Sub-leaf shards (core Lean only)

A witness leaf checked in parts, each part its own theorem (the kernel's caches live per declaration, so the parts
bound the memory of the kernel-only proofs): the head (exact checks, crossing radius, pins), the winding number, and
segments of the tile-arc records. `unit_of_parts` and `seg_step` put the parts of a unit back together.
-/

namespace C64Chk

open Ival Ival.Ball C64Num

/-- `k` tile-arc records from `(q₀, s)` pass, none of them the last one. -/
def taRun (g : Glob) (A : ACtx) (E : EllB) (r' tn td : Nat) (B : List Box4) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, q0, s =>
    taOK g A E r' tn td B q0 (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.1 (rdTA A.pins.length s).2.2.1
        (rdTA A.pins.length s).2.2.2.1 &&
      !((rdTA A.pins.length s).1 == 2 ^ g.EQ) &&
      taRun g A E r' tn td B k (rdTA A.pins.length s).1 (rdTA A.pins.length s).2.2.2.2

theorem checkTAs_of_run {g : Glob} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} :
    ∀ (k N q0 s : Nat), taRun g A E r' tn td B k q0 s = true →
      checkTAs g A E r' tn td B N (taSkip A.pins.length k q0 s).1 (taSkip A.pins.length k q0 s).2 = true →
      checkTAs g A E r' tn td B (N + k) q0 s = true
  | 0, _, _, _, _, h => h
  | k + 1, N, q0, s, hr, h => by
    simp only [taRun, Bool.and_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨⟨hok, hne⟩, hrun⟩ := hr
    have ih := checkTAs_of_run k N _ _ hrun h
    show checkTAs g A E r' tn td B ((N + k) + 1) q0 s = true
    simp only [checkTAs, hok, hne, ih, Bool.true_and, Bool.false_or]

theorem checkTAs_seg {g : Glob} {A : ACtx} {E : EllB} {r' tn td : Nat} {B : List Box4} {j k K s : Nat}
    (hr : taRun g A E r' tn td B k (taSkip A.pins.length j 0 s).1 (taSkip A.pins.length j 0 s).2 = true)
    (h : checkTAs g A E r' tn td B K (taSkip A.pins.length (j + k) 0 s).1
      (taSkip A.pins.length (j + k) 0 s).2 = true) :
    checkTAs g A E r' tn td B (K + k) (taSkip A.pins.length j 0 s).1 (taSkip A.pins.length j 0 s).2 = true := by
  rw [taSkip_add] at h
  exact checkTAs_of_run k K _ _ hr h

/-! ## The parts of a witness leaf -/

/-- The exact checks, the crossing radius and the pins. -/
def witHead (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) : Bool :=
  (tileOf g w.ti).any fun _ => (atomsOK w.as).any fun mm => witExact g w mm.1 mm.2 &&
    ((rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX).any fun r' =>
      (sumK g.cfg A.zc w.as).any fun wz => decide (A.r ≤ r') &&
        decide (normHi (CBall.sub wz (CBall.mulR g.P (w.sg.ball g.P) A.Sc)) ≤ r') &&
        pinsIn g.cfg w.as A.pins (pinBoxes g.P A.pins bx))

/-- The winding number. -/
def witWind (g : Glob) (w : WitD) : Bool :=
  (tileOf g w.ti).any fun E => (atomsOK w.as).any fun mm => windOdd g E w.as (Ball.cdiv (mm.1.toNat * 2 ^ g.P) mm.2)

/-- The tile-arc records `[j, j + k)`, none of them the last. -/
def witSeg (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) (j k : Nat) : Bool :=
  (tileOf g w.ti).any fun E => (rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX).any fun r' =>
    taRun g A E r' w.tw.n.toNat w.tw.d (pinBoxes g.P A.pins bx) k (taSkip A.pins.length j 0 w.dat).1
      (taSkip A.pins.length j 0 w.dat).2

/-- The `k` tile-arc records from `j` on, `j + k` records in all. -/
def witLast (g : Glob) (A : ACtx) (bx : List (Nat × Nat × Nat)) (w : WitD) (j k : Nat) : Bool :=
  decide (w.N = j + k) && ((tileOf g w.ti).any fun E =>
    (rBound g A.E1 w.tw.n.toNat w.tw.d A.s0 A.s1 A.sc A.zc A.Sc A.S1c w.rX).any fun r' =>
      checkTAs g A E r' w.tw.n.toNat w.tw.d (pinBoxes g.P A.pins bx) k (taSkip A.pins.length j 0 w.dat).1
        (taSkip A.pins.length j 0 w.dat).2)

theorem witOK_of_parts {g : Glob} {A : ACtx} {bx : List (Nat × Nat × Nat)} {w : WitD} {N : Nat}
    (h0 : witHead g A bx w = true) (h1 : witWind g w = true) (h3 : witLast g A bx w 0 N = true) :
    witOK g A bx w = true := by
  unfold witHead at h0
  unfold witWind at h1
  unfold witLast at h3
  rw [Bool.and_eq_true, decide_eq_true_eq, Nat.zero_add, taSkip_zero] at h3
  obtain ⟨hN, h3⟩ := h3
  obtain ⟨E, hE, h0⟩ := any_true h0
  obtain ⟨E1, hE1, h1⟩ := any_true h1
  obtain ⟨E3, hE3, h3⟩ := any_true h3
  cases Option.some.inj (hE1.symm.trans hE)
  cases Option.some.inj (hE3.symm.trans hE)
  obtain ⟨mm, hmm, h0⟩ := any_true h0
  obtain ⟨mm1, hmm1, h1⟩ := any_true h1
  cases Option.some.inj (hmm1.symm.trans hmm)
  rw [Bool.and_eq_true] at h0
  obtain ⟨hx, h0⟩ := h0
  obtain ⟨r', hr, h0⟩ := any_true h0
  obtain ⟨r3, hr3, h3⟩ := any_true h3
  cases Option.some.inj (hr3.symm.trans hr)
  obtain ⟨wz, hwz, h0⟩ := any_true h0
  rw [Bool.and_eq_true, Bool.and_eq_true] at h0
  rw [← hN] at h3
  unfold witOK
  refine any_of hE (any_of hmm ?_)
  rw [Bool.and_eq_true]
  refine ⟨hx, any_of hr (any_of hwz ?_)⟩
  unfold witBall
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨h0, h3⟩, h1⟩

theorem witLast_step {g : Glob} {A : ACtx} {bx : List (Nat × Nat × Nat)} {w : WitD} {j k K : Nat}
    (h2 : witSeg g A bx w j k = true) (h3 : witLast g A bx w (j + k) K = true) :
    witLast g A bx w j (K + k) = true := by
  unfold witSeg at h2
  unfold witLast at h3 ⊢
  rw [Bool.and_eq_true, decide_eq_true_eq] at h3
  obtain ⟨hN, h3⟩ := h3
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  obtain ⟨E, hE, h2⟩ := any_true h2
  obtain ⟨E3, hE3, h3⟩ := any_true h3
  cases Option.some.inj (hE3.symm.trans hE)
  obtain ⟨r', hr, h2⟩ := any_true h2
  obtain ⟨r3, hr3, h3⟩ := any_true h3
  cases Option.some.inj (hr3.symm.trans hr)
  exact any_of hE (any_of hr (checkTAs_seg h2 h3))

/-! ## Units by parts -/

/-- The head of a unit: of a witness leaf `witHead`, any other unit whole. -/
def uHead (g : Glob) (A : ACtx) (u : Tree × List (Nat × Nat × Nat)) : Bool :=
  match u.1 with
  | .wit dat => witHead g A u.2 (rdWit dat)
  | t => walk g A t u.2

def uWind (g : Glob) (_A : ACtx) (u : Tree × List (Nat × Nat × Nat)) : Bool :=
  match u.1 with
  | .wit dat => witWind g (rdWit dat)
  | _ => true

def uSeg (g : Glob) (A : ACtx) (j k : Nat) (u : Tree × List (Nat × Nat × Nat)) : Bool :=
  match u.1 with
  | .wit dat => witSeg g A u.2 (rdWit dat) j k
  | _ => true

def uLast (g : Glob) (A : ACtx) (j k : Nat) (u : Tree × List (Nat × Nat × Nat)) : Bool :=
  match u.1 with
  | .wit dat => witLast g A u.2 (rdWit dat) j k
  | _ => true

theorem unit_of_parts {g : Glob} {o : Option ACtx} {U : List (Tree × List (Nat × Nat × Nat))} {N : Nat}
    (h0 : o.any (fun A => U.all fun u => uHead g A u) = true)
    (h1 : o.any (fun A => U.all fun u => uWind g A u) = true)
    (h3 : o.any (fun A => U.all fun u => uLast g A 0 N u) = true) :
    o.any (fun A => U.all fun u => walk g A u.1 u.2) = true := by
  cases o with
  | none => simp at h0
  | some A =>
    simp only [Option.any_some, List.all_eq_true] at h0 h1 h3 ⊢
    intro u hu
    have a0 := h0 u hu
    have a1 := h1 u hu
    have a3 := h3 u hu
    rcases u with ⟨t, bx⟩
    cases t with
    | wit dat => exact witOK_of_parts (N := N) a0 a1 a3
    | excl dat => exact a0
    | split j c0 c1 c2 c3 => exact a0

theorem seg_step {g : Glob} {o : Option ACtx} {U : List (Tree × List (Nat × Nat × Nat))} {j k K : Nat}
    (h2 : o.any (fun A => U.all fun u => uSeg g A j k u) = true)
    (h3 : o.any (fun A => U.all fun u => uLast g A (j + k) K u) = true) :
    o.any (fun A => U.all fun u => uLast g A j (K + k) u) = true := by
  cases o with
  | none => simp at h2
  | some A =>
    simp only [Option.any_some, List.all_eq_true] at h2 h3 ⊢
    intro u hu
    have a2 := h2 u hu
    have a3 := h3 u hu
    rcases u with ⟨t, bx⟩
    cases t with
    | wit dat => exact witLast_step a2 a3
    | excl dat => rfl
    | split j c0 c1 c2 c3 => rfl

end C64Chk
