import AutocorrCert.Checker

/-!
# Decoder for the exported certificate segments (untrusted, native only)

The decoder only produces the data the checker inspects; the soundness theorem quantifies over
whatever it returns, so it needs no proof.  Format: see `tools/export.py`.
-/

namespace Autocorr.Cert.Dec

/-- Value of a base64-alphabet character. -/
@[inline] def cval (c : UInt8) : Nat :=
  if 65 ≤ c && c ≤ 90 then (c - 65).toNat
  else if 97 ≤ c && c ≤ 122 then (c - 71).toNat
  else if 48 ≤ c && c ≤ 57 then (c + 4).toNat
  else if c == 43 then 62 else 63

/-- Unsigned little-endian base-32 varint at byte `i`; returns the value and the next position. -/
partial def readU (b : ByteArray) (i acc mul : Nat) : Nat × Nat :=
  if h : i < b.size then
    let v := cval b[i]
    if v < 32 then (acc + v * mul, i + 1) else readU b (i + 1) (acc + (v - 32) * mul) (mul * 32)
  else (acc, i)

def readI (b : ByteArray) (i : Nat) : Int × Nat :=
  let r := readU b i 0 1
  (if r.1 % 2 = 0 then Int.ofNat (r.1 / 2) else -Int.ofNat ((r.1 + 1) / 2), r.2)

def readN (b : ByteArray) (i : Nat) : Nat × Nat :=
  let r := readI b i
  (r.1.toNat, r.2)

def readMany {α : Type} (rd : Nat → α × Nat) : Nat → Nat → Array α → Array α × Nat
  | 0, i, acc => (acc, i)
  | k + 1, i, acc => let r := rd i; readMany rd k r.2 (acc.push r.1)

def scale : Rat := (2 : Rat) ^ 30

def readScaled (b : ByteArray) (i : Nat) : Rat × Nat :=
  let r := readI b i
  ((r.1 : Rat) / scale, r.2)

def readBox (nB : Nat) (b : ByteArray) (i : Nat) : Box × Nat :=
  let rL := readMany (readScaled b) nB i #[]
  let rU := readMany (readScaled b) nB rL.2 #[]
  (⟨rL.1, rU.1⟩, rU.2)

def readStack (nB : Nat) (b : ByteArray) (i : Nat) : List Box × Nat :=
  let rc := readN b i
  let r := readMany (readBox nB b) rc.1 rc.2 #[]
  (r.1.toList, r.2)

def readKey (b : ByteArray) (i : Nat) : RowKey × Nat :=
  let rk := readN b i
  match rk.1 with
  | 0 => let a := readN b rk.2; let c := readN b a.2; (.win a.1 c.1, c.2)
  | 1 => let a := readN b rk.2; (.P a.1, a.2)
  | 2 => let a := readN b rk.2; (.G a.1, a.2)
  | 3 => let a := readN b rk.2; (.tree a.1, a.2)
  | 4 => let a := readN b rk.2; let c := readN b a.2; let d := readN b c.2; (.ZA a.1 c.1 d.1, d.2)
  | 5 => let a := readN b rk.2; (.rlt a.1, a.2)
  | 6 => (.sym, rk.2)
  | _ => let a := readN b rk.2; let c := readN b a.2; let d := readN b c.2; (.mc a.1 c.1 d.1, d.2)

def readDual (b : ByteArray) (i : Nat) : (RowKey × Rat) × Nat :=
  let k := readKey b i
  let num := readI b k.2
  let e := readN b num.2
  ((k.1, mkRat num.1 (2 ^ e.1)), e.2)

def readRec (b : ByteArray) (i : Nat) : Rec × Nat :=
  let t := readN b i
  match t.1 with
  | 0 => let bb := readN b t.2; let s := readScaled b bb.2; (.split bb.1 s.1, s.2)
  | 1 => let m := readN b t.2; let ys := readMany (readDual b) m.1 m.2 #[]; (.leaf ys.1.toList, ys.2)
  | 2 => let m := readN b t.2; let ys := readMany (readDual b) m.1 m.2 #[]; (.farkas ys.1.toList, ys.2)
  | _ => (.deleg, t.2)

/-- A decoded segment: `(n, lam, stkIn, recs, stkOut)`. -/
structure Seg where
  n : Nat
  lam : Rat
  stkIn : List Box
  recs : List Rec
  stkOut : List Box

def decode (s : String) : Seg :=
  let b := s.toUTF8
  let v := readN b 0
  let n := readN b v.2
  let ln := readI b n.2
  let ld := readN b ln.2
  let nB := (mkSpec n.1).nB
  let si := readStack nB b ld.2
  let nr := readN b si.2
  let rs := readMany (readRec b) nr.1 nr.2 #[]
  let so := readStack nB b rs.2
  ⟨n.1, mkRat ln.1 ld.1, si.1, rs.1.toList, so.1⟩

def readStep (b : ByteArray) (i : Nat) : (Nat × Rat × Bool) × Nat :=
  let bb := readN b i
  let sv := readScaled b bb.2
  let sd := readN b sv.2
  ((bb.1, sv.1, sd.1 == 1), sd.2)

/-- A path: `len (b s_num side)*`; the empty string is the root. -/
def decodePath (s : String) : Path :=
  if s.isEmpty then [] else
    let b := s.toUTF8
    let len := readN b 0
    (readMany (readStep b) len.1 len.2 #[]).1.toList

/-- A record list: `count rec*`. -/
def decodeRecs (s : String) : List Rec :=
  let b := s.toUTF8
  let nr := readN b 0
  (readMany (readRec b) nr.1 nr.2 #[]).1.toList

end Autocorr.Cert.Dec

namespace Autocorr.Cert

/-- Check one exported segment string against the expected `n` and `lam`. -/
def checkSegStr (n : Nat) (lam : Rat) (stkIn stkOut : List Box) (s : String) : Bool :=
  let d := Dec.decode s
  d.n == n && d.lam == lam && d.stkIn == stkIn && d.stkOut == stkOut &&
    checkSeg (mkSpec n) lam stkIn d.recs stkOut

/-- A whole certificate in one segment: from the root box to the empty stack. -/
def checkWhole (n : Nat) (lam : Rat) (s : String) : Bool :=
  match rootBox (mkSpec n) with
  | some R => checkSegStr n lam [R] [] s
  | none => false

end Autocorr.Cert

namespace Autocorr.Cert

/-- Check one exported job (strings for the root path, the delegated paths and the records). -/
def checkJobStr (n : Nat) (lam : Rat) (root : String) (children : List String) (recs : String) : Bool :=
  checkJob (mkSpec n) lam (Dec.decodePath root) (children.map Dec.decodePath) (Dec.decodeRecs recs)

/-- The subtree at path `root` is covered: its job is accepted and all delegated subtrees are covered.
This composes the jobs of a certificate without any real analysis (core Lean only). -/
inductive Covered (n : Nat) (lam : Rat) : String → Prop where
  | mk (root : String) (children : List String) (recs : String)
      (h : checkJobStr n lam root children recs = true)
      (hc : ∀ c ∈ children, Covered n lam c) : Covered n lam root

end Autocorr.Cert

namespace Autocorr.Cert

/-- All paths of the list are covered (nested conjunction, convenient for literal lists). -/
def AllCovered (n : Nat) (lam : Rat) : List String → Prop
  | [] => True
  | c :: cs => Covered n lam c ∧ AllCovered n lam cs

theorem AllCovered.mem {n : Nat} {lam : Rat} : ∀ {l : List String}, AllCovered n lam l →
    ∀ c ∈ l, Covered n lam c
  | [], _, c, hc => absurd hc (List.not_mem_nil)
  | _ :: _, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h.1
    · exact AllCovered.mem h.2 c hc'

end Autocorr.Cert
