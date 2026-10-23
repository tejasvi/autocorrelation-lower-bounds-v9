import C64Core.Check

/-!
# Leaf-tree shards (core Lean only)

The walk over the leaf tree of an H arc split into separately checked pieces, for the kernel-only proofs. A `Cut`
marks subtrees of the leaf tree ("units"); `cutOK` checks the split nodes above them. Any walk-like function `W`
(the checker's `walk g A`, or a function with the same equation on split nodes) is true on the tree once it is
true on every unit (`walk_of_cut`). The units are checked in groups, ranges `[a, b)` of the unit list
(`unitsIn`), each group in its own module, joined by `groups_join` and closed by `arc_of_groups`.
-/

namespace C64Chk

/-- A cut of a leaf tree: `here` is one unit (a subtree checked as a whole), `down` a split node with cuts of its
four children. -/
inductive Cut where
  | here
  | down (c0 c1 c2 c3 : Cut)

/-- The pin boxes of the `n`-th child of a split on pin `j`. -/
def kidBx (j : Nat) (bx : List (Nat × Nat × Nat)) (n : Nat) : List (Nat × Nat × Nat) :=
  bx.set j (kid (bx.getD j (0, 0, 0)) n)

/-- Every `down` of the cut sits on a split node with a valid pin index. -/
def cutOK : Cut → Tree → List (Nat × Nat × Nat) → Bool
  | .here, _, _ => true
  | .down k0 k1 k2 k3, .split j c0 c1 c2 c3, bx =>
    decide (j < bx.length) && cutOK k0 c0 (kidBx j bx 0) && cutOK k1 c1 (kidBx j bx 1) &&
      cutOK k2 c2 (kidBx j bx 2) && cutOK k3 c3 (kidBx j bx 3)
  | .down _ _ _ _, _, _ => false

/-- The units of a cut, left to right, with their pin boxes. -/
def cutUnits : Cut → Tree → List (Nat × Nat × Nat) → List (Tree × List (Nat × Nat × Nat))
  | .here, t, bx => [(t, bx)]
  | .down k0 k1 k2 k3, .split j c0 c1 c2 c3, bx =>
    cutUnits k0 c0 (kidBx j bx 0) ++ cutUnits k1 c1 (kidBx j bx 1) ++ cutUnits k2 c2 (kidBx j bx 2) ++
      cutUnits k3 c3 (kidBx j bx 3)
  | .down _ _ _ _, _, _ => []

/-- The entries with indices in `[a, b)`. -/
def unitsIn {α : Type} (L : List α) (a b : Nat) : List α := (L.drop a).take (b - a)

theorem walk_of_cut {W : Tree → List (Nat × Nat × Nat) → Bool}
    (hW : ∀ j c0 c1 c2 c3 bx, W (.split j c0 c1 c2 c3) bx =
      (decide (j < bx.length) && W c0 (kidBx j bx 0) && W c1 (kidBx j bx 1) && W c2 (kidBx j bx 2) &&
        W c3 (kidBx j bx 3))) :
    ∀ (k : Cut) (t : Tree) (bx : List (Nat × Nat × Nat)), cutOK k t bx = true →
      (cutUnits k t bx).all (fun u => W u.1 u.2) = true → W t bx = true
  | .here, t, bx, _, h => by simpa [cutUnits] using h
  | .down k0 k1 k2 k3, .split j c0 c1 c2 c3, bx, hc, h => by
    simp only [cutOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [cutUnits, List.all_append, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hj, hc0⟩, hc1⟩, hc2⟩, hc3⟩ := hc
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    rw [hW, decide_eq_true hj, walk_of_cut hW k0 c0 _ hc0 h0, walk_of_cut hW k1 c1 _ hc1 h1,
      walk_of_cut hW k2 c2 _ hc2 h2, walk_of_cut hW k3 c3 _ hc3 h3]
    rfl
  | .down _ _ _ _, .excl _, _, hc, _ => by simp [cutOK] at hc
  | .down _ _ _ _, .wit _, _, hc, _ => by simp [cutOK] at hc

theorem unitsIn_append {α : Type} (L : List α) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    unitsIn L a c = unitsIn L a b ++ unitsIn L b c := by
  unfold unitsIn
  have e : c - a = (b - a) + (c - b) := by omega
  have e2 : a + (b - a) = b := by omega
  rw [e, List.take_add, List.drop_drop, e2]

theorem unitsIn_all {α : Type} (L : List α) {n : Nat} (hn : L.length = n) : unitsIn L 0 n = L := by
  unfold unitsIn
  rw [List.drop_zero, Nat.sub_zero, ← hn, List.take_length]

/-- Two adjacent groups of units of the same arc context. -/
theorem groups_join {β : Type} (o : Option β) (W : β → Tree → List (Nat × Nat × Nat) → Bool)
    (L : List (Tree × List (Nat × Nat × Nat))) {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : o.any (fun A => (unitsIn L a b).all (fun u => W A u.1 u.2)) = true)
    (h2 : o.any (fun A => (unitsIn L b c).all (fun u => W A u.1 u.2)) = true) :
    o.any (fun A => (unitsIn L a c).all (fun u => W A u.1 u.2)) = true := by
  cases o with
  | none => simp at h1
  | some A =>
    simp only [Option.any_some] at h1 h2 ⊢
    rw [unitsIn_append L hab hbc, List.all_append, h1, h2]
    rfl

/-- All units of a cut checked: the walk over the whole tree. -/
theorem arc_of_groups {β : Type} (o : Option β) (W : β → Tree → List (Nat × Nat × Nat) → Bool)
    (hW : ∀ A j c0 c1 c2 c3 bx, W A (.split j c0 c1 c2 c3) bx =
      (decide (j < bx.length) && W A c0 (kidBx j bx 0) && W A c1 (kidBx j bx 1) && W A c2 (kidBx j bx 2) &&
        W A c3 (kidBx j bx 3)))
    (k : Cut) (t : Tree) (bx : List (Nat × Nat × Nat)) (n : Nat) (hc : cutOK k t bx = true)
    (hn : (cutUnits k t bx).length = n)
    (h : o.any (fun A => (unitsIn (cutUnits k t bx) 0 n).all (fun u => W A u.1 u.2)) = true) :
    o.any (fun A => W A t bx) = true := by
  cases o with
  | none => simp at h
  | some A =>
    simp only [Option.any_some] at h ⊢
    rw [unitsIn_all _ hn] at h
    exact walk_of_cut (hW A) k t bx hc h

/-- The checker's walk satisfies the split equation. -/
theorem walk_split (g : Glob) (A : ACtx) (j : Nat) (c0 c1 c2 c3 : Tree) (bx : List (Nat × Nat × Nat)) :
    walk g A (.split j c0 c1 c2 c3) bx =
      (decide (j < bx.length) && walk g A c0 (kidBx j bx 0) && walk g A c1 (kidBx j bx 1) &&
        walk g A c2 (kidBx j bx 2) && walk g A c3 (kidBx j bx 3)) := rfl

/-- An H arc from its head and the walk over its tree. -/
theorem checkArc_H {g : Glob} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {t : Tree}
    (hh : hHead g s0 s1 sc pins Rs = true)
    (hw : (arcCtx g s0 s1 sc pins Rs rX).any (fun A => walk g A t (pins.map fun _ => (0, 0, 0))) = true) :
    checkArc g (.H s0 s1 sc pins Rs rX t) = true := by
  show (hHead g s0 s1 sc pins Rs && _) = true
  rw [hh, hw]; rfl

/-! ## Shared by the sub-leaf shards (C64Shard.Leaf, C64Shard.LeafK) -/

theorem any_true {α : Type} {p : α → Bool} : ∀ {o : Option α}, o.any p = true → ∃ a, o = some a ∧ p a = true
  | none, h => nomatch h
  | some a, h => ⟨a, rfl, h⟩

theorem any_of {α : Type} {p : α → Bool} {o : Option α} {a : α} (h : o = some a) (hp : p a = true) :
    o.any p = true := by
  subst h; exact hp

/-- The start `q` and the data of tile-arc record `k`, from record 0 at `(q₀, s)`. -/
def taSkip (m : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, q0, s => (q0, s)
  | k + 1, _, s => taSkip m k (rdTA m s).1 (rdTA m s).2.2.2.2

theorem taSkip_zero (m q0 s : Nat) : taSkip m 0 q0 s = (q0, s) := rfl

theorem taSkip_add (m : Nat) : ∀ (a b q0 s : Nat),
    taSkip m (a + b) q0 s = taSkip m b (taSkip m a q0 s).1 (taSkip m a q0 s).2
  | 0, b, q0, s => by rw [Nat.zero_add]; rfl
  | a + 1, b, q0, s => by
    rw [Nat.add_right_comm a 1 b]
    exact taSkip_add m a b (rdTA m s).1 (rdTA m s).2.2.2.2

end C64Chk
