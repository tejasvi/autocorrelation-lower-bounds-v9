import Lean

/-!
# `nat_b64% "…"`: a natural-number literal given in base64 (little-endian bytes)

Elaborates to the raw literal `Expr.lit (.natVal n)`, so the kernel sees a plain numeral.  The string is
data only: nothing about it is trusted (the theorems that use these numerals are checked by the kernel).
Conversion is divide and conquer, so it is quasi-linear in the length.
-/

namespace C64Core.Load

open Lean Elab Term

def b64val (c : Char) : Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then c.toNat - 65
  else if 'a' ≤ c ∧ c ≤ 'z' then c.toNat - 71
  else if '0' ≤ c ∧ c ≤ '9' then c.toNat + 4
  else if c = '+' then 62 else 63

/-- Little-endian bytes to a natural number, by halving. -/
partial def bytesToNat (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi - lo ≤ 16 then
    (List.range (hi - lo)).foldr (fun i acc => acc * 256 + (b.get! (lo + i)).toNat) 0
  else
    let mid := (lo + hi) / 2
    bytesToNat b lo mid + bytesToNat b mid hi * 256 ^ (mid - lo)

def decodeB64 (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray.filter (· ≠ '=')
  let mut out : ByteArray := ByteArray.emptyWithCapacity (cs.size * 3 / 4 + 3)
  let mut acc : Nat := 0
  let mut bits : Nat := 0
  for c in cs do
    acc := acc * 64 + b64val c
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push (acc / 2 ^ bits).toUInt8
      acc := acc % 2 ^ bits
  return out

syntax (name := natB64) "nat_b64% " str : term

@[term_elab natB64] def elabNatB64 : TermElab := fun stx _ => do
  match stx with
  | `(nat_b64% $s:str) =>
    let b := decodeB64 s.getString
    return mkRawNatLit (bytesToNat b 0 b.size)
  | _ => throwUnsupportedSyntax

end C64Core.Load
