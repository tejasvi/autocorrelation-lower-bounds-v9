import Autocorr.KSound.Box

/-!
# Contributions as lists of `(column, value)` and their packed / dotted forms

`packL L = Σ_{(c,v) ∈ L} v · 2^(136 c)` is what the kernel adds to an accumulator; `accD L` is the digit
vector; `dotL L x = Σ v · x_c`.
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

def packL (L : List (ℕ × ℕ)) : ℕ := (L.map (fun e => e.2 * 2 ^ (136 * e.1))).sum
def accD (L : List (ℕ × ℕ)) (c : ℕ) : ℕ := (L.map (fun e => if e.1 = c then e.2 else 0)).sum
noncomputable def dotL (L : List (ℕ × ℕ)) (x : ℕ → ℝ) : ℝ := (L.map (fun e => (e.2 : ℝ) * x e.1)).sum

@[simp] lemma packL_nil : packL [] = 0 := rfl
@[simp] lemma accD_nil (c : ℕ) : accD [] c = 0 := rfl
@[simp] lemma dotL_nil (x : ℕ → ℝ) : dotL [] x = 0 := rfl
@[simp] lemma packL_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    packL (e :: L) = e.2 * 2 ^ (136 * e.1) + packL L := by simp [packL]
@[simp] lemma accD_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) (c : ℕ) :
    accD (e :: L) c = (if e.1 = c then e.2 else 0) + accD L c := by simp [accD]
@[simp] lemma dotL_cons (e : ℕ × ℕ) (L : List (ℕ × ℕ)) (x : ℕ → ℝ) :
    dotL (e :: L) x = (e.2 : ℝ) * x e.1 + dotL L x := by simp [dotL]
lemma packL_append (L M : List (ℕ × ℕ)) : packL (L ++ M) = packL L + packL M := by simp [packL]
lemma accD_append (L M : List (ℕ × ℕ)) (c : ℕ) : accD (L ++ M) c = accD L c + accD M c := by simp [accD]
lemma dotL_append (L M : List (ℕ × ℕ)) (x : ℕ → ℝ) : dotL (L ++ M) x = dotL L x + dotL M x := by
  simp [dotL]

lemma packL_eq_pk {L : List (ℕ × ℕ)} {S : ℕ} (hL : ∀ e ∈ L, e.1 < S) : packL L = pk 136 (accD L) S := by
  induction L with
  | nil => simp [pk]
  | cons e L ih =>
    rw [packL_cons, ih (fun f hf => hL f (List.mem_cons_of_mem _ hf)),
      pk_single 136 e.2 e.1 S (hL e (List.mem_cons_self ..)), pk_add]
    refine pk_congr (fun c _ => ?_)
    rw [accD_cons]
    by_cases h : e.1 = c
    · simp [h]
    · simp [h, Ne.symm h]

lemma sum_accD {L : List (ℕ × ℕ)} {S : ℕ} (hL : ∀ e ∈ L, e.1 < S) (x : ℕ → ℝ) :
    ∑ c ∈ Finset.range S, (accD L c : ℝ) * x c = dotL L x := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [dotL_cons, ← ih (fun f hf => hL f (List.mem_cons_of_mem _ hf))]
    simp only [accD_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single e.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (hL e (List.mem_cons_self ..))) h

lemma accD_le {L : List (ℕ × ℕ)} {B : ℕ} (hL : ∀ e ∈ L, e.2 ≤ B) (c : ℕ) : accD L c ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [accD_cons, List.length_cons, add_mul, one_mul, add_comm (L.length * B)]
    have := ih (fun f hf => hL f (List.mem_cons_of_mem _ hf))
    have he := hL e (List.mem_cons_self ..)
    split_ifs <;> omega

/-- Scaling every value. -/
def scaleL (a : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) := L.map (fun e => (e.1, a * e.2))

lemma packL_scale (a : ℕ) (L : List (ℕ × ℕ)) : packL (scaleL a L) = a * packL L := by
  induction L with
  | nil => simp [scaleL]
  | cons e L ih =>
    simp only [scaleL, List.map_cons, packL_cons] at ih ⊢
    rw [ih]; ring

lemma dotL_scale (a : ℕ) (L : List (ℕ × ℕ)) (x : ℕ → ℝ) : dotL (scaleL a L) x = a * dotL L x := by
  induction L with
  | nil => simp [scaleL]
  | cons e L ih =>
    simp only [scaleL, List.map_cons, dotL_cons] at ih ⊢
    rw [ih]; push_cast; ring

lemma atc_eq (v c : ℕ) : atc v c = packL [(c, v)] := by
  simp [atc, raw_shiftLeft, raw_mul, Nat.shiftLeft_eq, packL]

lemma ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq.mpr h
lemma ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.ble_eq.mp hb) h

/-! ## Patterns -/

/-- The cells of `P(c)`: ordered entries `(i, c-i)`. -/
noncomputable def patPL (oZ n c : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | i + 1 => (if i ≤ c ∧ c - i < n then [(zIdxK oZ n i (c - i), 1)] else []) ++ patPL oZ n c i

noncomputable def patRL (oZ n i : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | j + 1 => (zIdxK oZ n i j, 1) :: patRL oZ n i j

lemma patP_eq' (oZ n c : ℕ) : ∀ k, (Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => sel (Nat.ble i c) (sel (Nat.ble (Nat.add (Nat.sub c i) 1) n)
      (Nat.add acc (atc 1 (zIdxK oZ n i (Nat.sub c i)))) acc) acc) k : ℕ) = packL (patPL oZ n c k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [patPL, packL_append]
    show sel (Nat.ble k c) (sel (Nat.ble (Nat.add (Nat.sub c k) 1) n) _ _) _ = _
    rw [ih]
    by_cases h1 : k ≤ c
    · by_cases h2 : c - k < n
      · rw [ble_true h1, ble_true (show Nat.add (Nat.sub c k) 1 ≤ n by simp only [raw_add, raw_sub]; omega),
          if_pos ⟨h1, h2⟩, atc_eq]
        simp [sel, add_comm, raw_sub, raw_add]
      · rw [ble_true h1, ble_false (show ¬ Nat.add (Nat.sub c k) 1 ≤ n by simp only [raw_add, raw_sub]; omega),
          if_neg (by omega)]
        simp [sel]
    · rw [ble_false h1, if_neg (by omega)]
      simp [sel]

lemma patP_eq (oZ n c : ℕ) : patP oZ n c = packL (patPL oZ n c n) := patP_eq' oZ n c n

lemma patR_eq' (oZ n i : ℕ) : ∀ k, (Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.add acc (atc 1 (zIdxK oZ n i j))) k : ℕ) = packL (patRL oZ n i k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show Nat.add _ (atc 1 _) = _
    rw [ih, atc_eq]; simp [patRL, raw_add, add_comm]

lemma patR_eq (oZ n i : ℕ) : patR oZ n i = packL (patRL oZ n i n) := patR_eq' oZ n i n

end AutocorrK
