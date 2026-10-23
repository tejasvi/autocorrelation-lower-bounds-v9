import AutocorrK.Core

/-!
# Composition of segment checks (core Lean)

`StkK P a b stk`: every box of the stack `stk` is covered, as established by kernel-checked segments
(`segCheck`), each of which turns the coverage of its output stack into the coverage of its input stack.
The generated certificate modules (core only, no Mathlib) prove `StkK P a b [box]` for every job root box;
`Autocorr.KSound.Run.stkK_sound` turns this into `StackOKK`.
-/

namespace AutocorrK

/-- `cnt` boxes packed in one literal (box `j` = `L | U << w` at bit `2 w j`, `w = 32 nB`): segment interfaces
are written this way to keep the number of declarations small.  Data only (no soundness content). -/
noncomputable def unpk (w cnt : Nat) : Nat → List (Nat × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun _ ih x => (Nat.mod x (Nat.pow 2 w), Nat.mod (Nat.shiftRight x w) (Nat.pow 2 w)) ::
      ih (Nat.shiftRight x (Nat.mul 2 w))) cnt

inductive StkK (P : KP) (a b : Nat) : List (Nat × Nat) → Prop
  | nil : StkK P a b []
  | cons {x : Nat × Nat} {xs : List (Nat × Nat)} : StkK P a b [x] → StkK P a b xs → StkK P a b (x :: xs)
  | seg {sin sout : List (Nat × Nat)} (nrec data : Nat) : segCheck P a b nrec data sin sout = true →
      StkK P a b sout → StkK P a b sin

end AutocorrK
