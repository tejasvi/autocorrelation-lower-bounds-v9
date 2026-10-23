import AutocorrCert.CheckerX
import AutocorrCert.Decode

/-!
# Decoder for the extended format (square-cut keys: tag 8, `v0 m (block v)*m`); untrusted, native only
-/

namespace Autocorr.Cert.Dec

def readTerm (b : ByteArray) (i : Nat) : (Nat × Int) × Nat :=
  let bb := readN b i
  let v := readI b bb.2
  ((bb.1, v.1), v.2)

def readKeyX (b : ByteArray) (i : Nat) : XKey × Nat :=
  let rk := readN b i
  if rk.1 == 8 then
    let v0 := readI b rk.2
    let m := readN b v0.2
    let ts := readMany (readTerm b) m.1 m.2 #[]
    (.sq v0.1 ts.1.toList, ts.2)
  else
    let k := readKey b i
    (.base k.1, k.2)

def readDualX (b : ByteArray) (i : Nat) : (XKey × Rat) × Nat :=
  let k := readKeyX b i
  let num := readI b k.2
  let e := readN b num.2
  ((k.1, mkRat num.1 (2 ^ e.1)), e.2)

def readRecX (b : ByteArray) (i : Nat) : RecX × Nat :=
  let t := readN b i
  match t.1 with
  | 0 => let bb := readN b t.2; let s := readScaled b bb.2; (.split bb.1 s.1, s.2)
  | 1 => let m := readN b t.2; let ys := readMany (readDualX b) m.1 m.2 #[]; (.leaf ys.1.toList, ys.2)
  | 2 => let m := readN b t.2; let ys := readMany (readDualX b) m.1 m.2 #[]; (.farkas ys.1.toList, ys.2)
  | 3 => (.deleg, t.2)
  | _ => let m := readN b t.2; let ys := readMany (readDualX b) m.1 m.2 #[]; (.leafc ys.1.toList, ys.2)

def decodeRecsX (s : String) : List RecX :=
  let b := s.toUTF8
  let nr := readN b 0
  (readMany (readRecX b) nr.1 nr.2 #[]).1.toList

/-- A key list: `count key*` (the ZA rows in completion order). -/
def decodeKeys (s : String) : List RowKey :=
  let b := s.toUTF8
  let nr := readN b 0
  (readMany (readKey b) nr.1 nr.2 #[]).1.toList

end Autocorr.Cert.Dec

namespace Autocorr.Cert

def checkJobStrX (n : Nat) (lam : Rat) (zo : String) (root : String) (children : List String) (recs : String) :
    Bool :=
  checkJobX (mkSpec n) lam (Dec.decodeKeys zo) (Dec.decodePath root) (children.map Dec.decodePath)
    (Dec.decodeRecsX recs)

/-- As `Covered`, for the extended checker. -/
inductive CoveredX (n : Nat) (lam : Rat) (zo : String) : String → Prop where
  | mk (root : String) (children : List String) (recs : String)
      (h : checkJobStrX n lam zo root children recs = true)
      (hc : ∀ c ∈ children, CoveredX n lam zo c) : CoveredX n lam zo root

def AllCoveredX (n : Nat) (lam : Rat) (zo : String) : List String → Prop
  | [] => True
  | c :: cs => CoveredX n lam zo c ∧ AllCoveredX n lam zo cs

theorem AllCoveredX.mem {n : Nat} {lam : Rat} {zo : String} : ∀ {l : List String}, AllCoveredX n lam zo l →
    ∀ c ∈ l, CoveredX n lam zo c
  | [], _, c, hc => absurd hc (List.not_mem_nil)
  | _ :: _, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h.1
    · exact AllCoveredX.mem h.2 c hc'

end Autocorr.Cert
