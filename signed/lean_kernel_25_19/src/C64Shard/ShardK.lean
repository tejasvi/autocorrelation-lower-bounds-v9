import C64Shard.Shard
import C64K.KChk

/-!
# Leaf-tree shards for the kernel port `C64KChk` (core Lean only)

The port's walk has the split equation of `walk_of_cut`, and an H arc passes from its head and the walk over its
tree, as for the checker (`C64Chk.walk_split`, `C64Chk.checkArc_H`).
-/

namespace C64KChk

open KIval KIval.KBall KNum C64Chk

theorem walk_split (g : Glob) (A : ACtx) (j : Nat) (c0 c1 c2 c3 : Tree) (bx : List (Nat × Nat × Nat)) :
    walk g A (.split j c0 c1 c2 c3) bx =
      (decide (j < bx.length) && walk g A c0 (kidBx j bx 0) && walk g A c1 (kidBx j bx 1) &&
        walk g A c2 (kidBx j bx 2) && walk g A c3 (kidBx j bx 3)) := rfl

theorem checkArc_H {g : Glob} {s0 s1 sc : Nat} {pins : List (Q × Q)} {Rs : List Q} {rX : Nat} {t : Tree}
    (hh : hHead g s0 s1 sc pins Rs = true)
    (hw : (arcCtx g s0 s1 sc pins Rs rX).any (fun A => walk g A t (pins.map fun _ => (0, 0, 0))) = true) :
    checkArc g (.H s0 s1 sc pins Rs rX t) = true := by
  show (hHead g s0 s1 sc pins Rs && _) = true
  rw [hh, hw]; rfl

end C64KChk
