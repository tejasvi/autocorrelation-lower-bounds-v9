import AutocorrK.Core
import AutocorrCert.Checker

/-!
# One-time checks of the kernel checker's constants against `Autocorr.Cert.Spec`

`kpOK sp P` is evaluated by the kernel once per `n`.  Each check states, in the form the soundness proof
uses, that the packed tables of `P` describe genuine rows of the LP of `Autocorr.Cert.rowOf` (with the
window rows rescaled) and genuine internal blocks of the block tree.
-/

namespace AutocorrK

open Autocorr.Cert

noncomputable section

/-- Key field `i` (7 bits) of a descriptor. -/
def kf (d i : Nat) : Nat := Nat.mod (Nat.shiftRight d (Nat.add 52 (Nat.mul 7 i))) 128

/-- The descriptor `d` describes a valid row (fields as used by `step`). -/
def descOK (sp : Spec) (d : Nat) : Bool :=
  let kind := Nat.mod d 8
  let k0 := kf d 0
  let k1 := kf d 1
  let k2 := kf d 2
  sel (Nat.beq kind 0)
    (keyOK sp (.win k0 k1) && Nat.beq (f12 d 0) (Nat.add sp.oG k1) &&
      (dflag d == decide (0 < k0)) && (Nat.beq k0 0 || Nat.beq (f12 d 1) (Nat.add sp.oG (Nat.sub k0 1))) &&
      Nat.beq (f12 d 2) (Nat.add (Nat.sub k1 k0) 2))
  (sel (Nat.beq kind 1)
    (keyOK sp (.P k0) && Nat.beq (f12 d 0) (Nat.add sp.oP k0) && Nat.beq (f12 d 1) k0)
  (sel (Nat.beq kind 2)
    (keyOK sp (.G k0) && Nat.beq (f12 d 0) (Nat.add sp.oG k0) && Nat.beq (f12 d 1) (Nat.add sp.oP k0) &&
      (dflag d == decide (0 < k0)) && (Nat.beq k0 0 || Nat.beq (f12 d 2) (Nat.add sp.oG (Nat.sub k0 1))))
  (sel (Nat.beq kind 3)
    (keyOK sp (.tree k0) && Nat.beq (f12 d 0) k0 && Nat.beq (f12 d 1) (sp.blk k0).c1 &&
      Nat.beq (f12 d 2) (sp.blk k0).c2)
  (sel (Nat.beq kind 4)
    (keyOK sp (.ZA k0 k1 k2) && Nat.beq (f12 d 0) (sp.canon k0 k1) && (dflag d == decide (k0 = k1)) &&
      (sel (Nat.beq k0 k1)
        (Nat.beq (f12 d 1) (sp.canon (sp.blk k2).c1 (sp.blk k2).c1) &&
          Nat.beq (f12 d 2) (sp.canon (sp.blk k2).c2 (sp.blk k2).c2) &&
          Nat.beq (f12 d 3) (sp.canon (sp.blk k2).c1 (sp.blk k2).c2))
        (Nat.beq (f12 d 1) (sp.canon (sp.blk k2).c1 (sel (Nat.beq k2 k0) k1 k0)) &&
          Nat.beq (f12 d 2) (sp.canon (sp.blk k2).c2 (sel (Nat.beq k2 k0) k1 k0)))))
  (sel (Nat.beq kind 5)
    (keyOK sp (.rlt k0) && Nat.beq (f12 d 0) k0 && Nat.beq (f12 d 1) (sp.leaf k0))
  (sel (Nat.beq kind 6)
    true
    (keyOK sp (.mc k0 k1 k2) && Nat.beq (f12 d 0) (sp.canon k0 k1) && Nat.beq (f12 d 1) k0 &&
      Nat.beq (f12 d 2) k1 && Nat.beq (f12 d 3) k2 && (dflag d == decide (k0 = k1)))))))))

/-- All descriptors `r < NR` are valid. -/
def tableOK (sp : Spec) (P : KP) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => descOK sp (desc P r) && ih) P.NR

/-- The packed sym pattern: digit `leaf i` holds `|2i - (n-1)| · 2^30` in `symP` or `symN`. -/
def symRef (sp : Spec) (pos : Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc
      (sel pos
        (sel (Nat.ble sp.n (Nat.mul 2 i))
          (atc (Nat.shiftLeft (Nat.sub (Nat.mul 2 i) (Nat.sub sp.n 1)) 30) (sp.leaf i)) 0)
        (sel (Nat.ble (Nat.add (Nat.mul 2 i) 2) sp.n)
          (atc (Nat.shiftLeft (Nat.sub (Nat.sub sp.n 1) (Nat.mul 2 i)) 30) (sp.leaf i)) 0)))
    sp.n

/-- Every listed internal-block entry `(b, c1, c2)` is an internal block with its children. -/
def intOK (sp : Spec) (P : KP) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih tab =>
      let e := Nat.mod tab 2097152
      let b := Nat.mod e 128
      Nat.blt b sp.nB && sp.isInt b && Nat.beq (Nat.mod (Nat.shiftRight e 7) 128) (sp.blk b).c1 &&
        Nat.beq (Nat.shiftRight e 14) (sp.blk b).c2 && ih (Nat.shiftRight tab 21))
    P.nInt P.intTab

/-- All constants of `P` agree with the block tree `sp`. -/
def kpOK (sp : Spec) (P : KP) : Bool :=
  sp.wf && Nat.beq P.n sp.n && Nat.beq P.nB sp.nB && Nat.beq P.oZ sp.oZ && Nat.beq P.oP sp.oP &&
    Nat.beq P.oG sp.oG && Nat.beq P.NC1 sp.oT && Nat.blt P.n 64 && Nat.blt P.nB 128 &&
    Nat.blt P.NR 16384 && Nat.ble sp.NC 4096 && tableOK sp P && Nat.beq P.symP (symRef sp true) &&
    Nat.beq P.symN (symRef sp false) && intOK sp P

end

end AutocorrK
