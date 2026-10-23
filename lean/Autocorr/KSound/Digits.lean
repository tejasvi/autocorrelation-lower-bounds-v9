import Mathlib
import AutocorrK.Core

/-!
# Packed digit vectors

`pk w v s = Σ_{c<s} v c · 2^(w c)`.  Linearity holds for arbitrary digits; extraction of a digit needs all
digits `< 2^w`.  Also: the 32-bit slot update `set32`, and the SWAR identity used by `swarNeg`.
-/

namespace AutocorrK

open scoped BigOperators

/-! Raw `Nat` functions (used by the kernel checker) as operators. -/
lemma raw_add (a b : ℕ) : Nat.add a b = a + b := rfl
lemma raw_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
lemma raw_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
lemma raw_div (a b : ℕ) : Nat.div a b = a / b := rfl
lemma raw_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
lemma raw_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl
lemma raw_land (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma raw_shiftLeft (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
lemma raw_shiftRight (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

/-- `Σ_{c<s} v c · 2^(w c)` -/
def pk (w : ℕ) (v : ℕ → ℕ) (s : ℕ) : ℕ := ∑ c ∈ Finset.range s, v c * 2 ^ (w * c)

lemma pk_succ (w : ℕ) (v : ℕ → ℕ) (s : ℕ) : pk w v (s + 1) = pk w v s + v s * 2 ^ (w * s) := by
  simp [pk, Finset.sum_range_succ]

lemma pk_zero (w : ℕ) (v : ℕ → ℕ) : pk w v 0 = 0 := by simp [pk]

lemma pk_add (w : ℕ) (u v : ℕ → ℕ) (s : ℕ) : pk w u s + pk w v s = pk w (fun c => u c + v c) s := by
  simp [pk, add_mul, Finset.sum_add_distrib]

lemma pk_mul (w : ℕ) (a : ℕ) (v : ℕ → ℕ) (s : ℕ) : a * pk w v s = pk w (fun c => a * v c) s := by
  simp [pk, Finset.mul_sum, mul_assoc]

lemma pk_congr {w : ℕ} {u v : ℕ → ℕ} {s : ℕ} (h : ∀ c < s, u c = v c) : pk w u s = pk w v s :=
  Finset.sum_congr rfl (fun c hc => by rw [h c (Finset.mem_range.mp hc)])

/-- A single digit. -/
lemma pk_single (w : ℕ) (a c s : ℕ) (hc : c < s) :
    a * 2 ^ (w * c) = pk w (fun i => if i = c then a else 0) s := by
  unfold pk
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_range.mpr hc) h

lemma pk_lt {w : ℕ} {v : ℕ → ℕ} {s : ℕ} (hv : ∀ c < s, v c < 2 ^ w) : pk w v s < 2 ^ (w * s) := by
  induction s with
  | zero => simp [pk]
  | succ s ih =>
    rw [pk_succ]
    have h1 := ih (fun c hc => hv c (by omega))
    have h2 : v s ≤ 2 ^ w - 1 := Nat.le_sub_one_of_lt (hv s (by omega))
    have h3 : v s * 2 ^ (w * s) ≤ (2 ^ w - 1) * 2 ^ (w * s) := Nat.mul_le_mul_right _ h2
    have h4 : (2 ^ w - 1) * 2 ^ (w * s) + 2 ^ (w * s) = 2 ^ (w * (s + 1)) := by
      have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by omega)),
        ← pow_add, mul_add, mul_one, add_comm]
    omega

lemma pk_split (w : ℕ) (v : ℕ → ℕ) (k j : ℕ) :
    pk w v (k + j) = pk w v k + 2 ^ (w * k) * pk w (fun c => v (c + k)) j := by
  induction j with
  | zero => simp [pk]
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 by omega, pk_succ, ih, pk_succ,
      show k + j = j + k from add_comm k j, mul_add w j k, pow_add]
    ring

/-- Low part: `pk w v s % 2^(w k) = pk w v k` for `k ≤ s`. -/
lemma pk_mod {w : ℕ} {v : ℕ → ℕ} {s k : ℕ} (hv : ∀ c < s, v c < 2 ^ w) (hk : k ≤ s) :
    pk w v s % 2 ^ (w * k) = pk w v k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsplit : pk w v (k + j) = pk w v k + 2 ^ (w * k) * pk w (fun c => v (c + k)) j :=
    pk_split w v k j
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (pk_lt (fun c hc => hv c (by omega)))]

/-- High part: `pk w v s / 2^(w k) = pk w (v (· + k)) (s - k)` for `k ≤ s`. -/
lemma pk_div {w : ℕ} {v : ℕ → ℕ} {s k : ℕ} (hv : ∀ c < s, v c < 2 ^ w) (hk : k ≤ s) :
    pk w v s / 2 ^ (w * k) = pk w (fun c => v (c + k)) (s - k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsplit : pk w v (k + j) = pk w v k + 2 ^ (w * k) * pk w (fun c => v (c + k)) j :=
    pk_split w v k j
  rw [hsplit, show k + j - k = j by omega, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (pk_lt (fun c hc => hv c (by omega))), zero_add]

/-- Digit extraction. -/
lemma pk_digit {w : ℕ} {v : ℕ → ℕ} {s j : ℕ} (hv : ∀ c < s, v c < 2 ^ w) (hj : j < s) :
    pk w v s / 2 ^ (w * j) % 2 ^ w = v j := by
  rw [pk_div hv hj.le]
  have hv' : ∀ c < s - j, v (c + j) < 2 ^ w := fun c hc => hv _ (by omega)
  have := pk_mod (k := 1) hv' (by omega)
  rw [mul_one] at this
  rw [this]
  simp [pk]

/-- Mod `2^w - 1` sums the digits. -/
lemma pk_mod_pred (w : ℕ) (v : ℕ → ℕ) (s : ℕ) :
    pk w v s % (2 ^ w - 1) = (∑ c ∈ Finset.range s, v c) % (2 ^ w - 1) := by
  have h1 : 2 ^ w ≡ 1 [MOD 2 ^ w - 1] := Nat.modEq_sub Nat.one_le_two_pow
  induction s with
  | zero => simp [pk]
  | succ s ih =>
    rw [pk_succ, Finset.sum_range_succ]
    refine Nat.ModEq.add ih ?_
    have h2 : 2 ^ (w * s) ≡ 1 [MOD 2 ^ w - 1] := by
      rw [pow_mul]; simpa using h1.pow s
    simpa using Nat.ModEq.mul_left (v s) h2

/-! ## Bitwise and on aligned digits -/

lemma land_lt_two_pow {a b K : ℕ} (ha : a < 2 ^ K) : a &&& b < 2 ^ K := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_land, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi)),
    Bool.false_and]

lemma land_split {a b a' b' K : ℕ} (ha : a < 2 ^ K) (ha' : a' < 2 ^ K) :
    (2 ^ K * b + a) &&& (2 ^ K * b' + a') = 2 ^ K * (b &&& b') + (a &&& a') := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ ha',
    Nat.testBit_two_pow_mul_add _ (land_lt_two_pow ha)]
  split_ifs <;> simp

lemma pk_land {w : ℕ} {x y : ℕ → ℕ} {s : ℕ} (hx : ∀ c < s, x c < 2 ^ w) (hy : ∀ c < s, y c < 2 ^ w) :
    pk w x s &&& pk w y s = pk w (fun c => x c &&& y c) s := by
  induction s with
  | zero => simp [pk]
  | succ s ih =>
    rw [pk_succ, pk_succ, pk_succ, add_comm (pk w x s), add_comm (pk w y s), mul_comm (x s),
      mul_comm (y s), land_split (pk_lt (fun c hc => hx c (by omega)))
        (pk_lt (fun c hc => hy c (by omega))),
      ih (fun c hc => hx c (by omega)) (fun c hc => hy c (by omega))]
    ring

lemma pk_sub {w : ℕ} {u v : ℕ → ℕ} {s : ℕ} (h : ∀ c < s, v c ≤ u c) :
    pk w u s - pk w v s = pk w (fun c => u c - v c) s := by
  have : pk w u s = pk w (fun c => u c - v c) s + pk w v s := by
    rw [pk_add]; exact pk_congr (fun c hc => by have := h c hc; omega)
  omega

/-- `pk 136 (fun _ => 1) s = (2^(136 s) - 1) / (2^136 - 1)` -/
lemma pk_ones (s : ℕ) : (2 ^ (136 * s) - 1) / W1 = pk 136 (fun _ => 1) s := by
  have hW : W1 = 2 ^ 136 - 1 := by norm_num [W1]
  have key : pk 136 (fun _ => 1) s * W1 = 2 ^ (136 * s) - 1 := by
    induction s with
    | zero => simp [pk]
    | succ s ih =>
      rw [pk_succ, add_mul, ih, hW, one_mul, mul_add, pow_add]
      have h1 : 1 ≤ 2 ^ (136 * s) := Nat.one_le_two_pow
      have h2 : 1 ≤ (2 : ℕ) ^ 136 := Nat.one_le_two_pow
      rw [Nat.mul_sub, mul_one, mul_one]
      have h3 : 2 ^ (136 * s) ≤ 2 ^ (136 * s) * 2 ^ 136 := Nat.le_mul_of_pos_right _ (by positivity)
      omega
  rw [← key, Nat.mul_div_cancel _ (by norm_num [W1])]

/-- The SWAR identity of `swarNeg`. -/
theorem swarNeg_eq (s : ℕ) (P N : ℕ → ℕ) (hP : ∀ c < s, P c < 2 ^ 135) (hN : ∀ c < s, N c < 2 ^ 135)
    (hsum : ∑ c ∈ Finset.range s, (N c - P c) < W1) :
    swarNeg s (pk 136 P s) (pk 136 N s) = ∑ c ∈ Finset.range s, (N c - P c) := by
  have hW : W1 = 2 ^ 136 - 1 := by norm_num [W1]
  have h135 : (2 : ℕ) ^ 135 < 2 ^ 136 := by norm_num
  unfold swarNeg
  simp only [raw_add, raw_sub, raw_mul, raw_div, raw_mod, raw_pow, raw_land, raw_shiftLeft,
    raw_shiftRight]
  rw [pk_ones]
  -- H
  have hH : (pk 136 (fun _ => 1) s) <<< 135 = pk 136 (fun _ => 2 ^ 135) s := by
    rw [Nat.shiftLeft_eq, mul_comm, pk_mul]; simp
  rw [hH]
  -- X
  set D : ℕ → ℕ := fun c => 2 ^ 135 + N c - P c with hD
  have hX : pk 136 N s + pk 136 (fun _ => 2 ^ 135) s - pk 136 P s = pk 136 D s := by
    rw [pk_add, pk_sub]
    · exact pk_congr (fun c _ => by simp only [hD]; omega)
    · intro c hc; have := hP c hc; omega
  rw [hX]
  have hDlt : ∀ c < s, D c < 2 ^ 136 := fun c hc => by
    have := hP c hc; have := hN c hc; simp only [hD]; omega
  have hHlt : ∀ c < s, (2 : ℕ) ^ 135 < 2 ^ 136 := fun _ _ => h135
  -- guard bits
  have hdig : ∀ c < s, D c &&& 2 ^ 135 = 2 ^ 135 * (if P c ≤ N c then 1 else 0) := by
    intro c hc
    have hP' := hP c hc; have hN' := hN c hc
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_land, Nat.testBit_two_pow]
    split_ifs with hle
    · rw [mul_one, Nat.testBit_two_pow]
      by_cases hi : 135 = i
      · subst hi
        have hy : N c - P c < 2 ^ 135 := by omega
        have hDc : D c = 2 ^ 135 * 1 + (N c - P c) := by simp only [hD]; omega
        rw [hDc, Nat.testBit_two_pow_mul_add _ hy]
        simp
      · simp [hi]
    · rw [mul_zero, Nat.zero_testBit]
      by_cases hi : 135 = i
      · subst hi
        have h2 : D c < 2 ^ 135 := by simp only [hD]; omega
        rw [Nat.testBit_lt_two_pow h2]; simp
      · simp [hi]
  have hG : (pk 136 D s &&& pk 136 (fun _ => 2 ^ 135) s) >>> 135 =
      pk 136 (fun c => if P c ≤ N c then 1 else 0) s := by
    rw [pk_land hDlt hHlt, pk_congr (w := 136) (v := fun c => 2 ^ 135 * (if P c ≤ N c then 1 else 0))
      (fun c hc => hdig c hc), ← pk_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by positivity)]
  rw [hG, mul_comm, pk_mul]
  set M : ℕ → ℕ := fun c => W1 * (if P c ≤ N c then 1 else 0) with hM
  have hMlt : ∀ c < s, M c < 2 ^ 136 := fun c _ => by
    simp only [hM]; split_ifs <;> norm_num [W1]
  have hW1 : ∀ x, x < 2 ^ 136 → x &&& W1 = x := fun x hx => by
    rw [hW, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  rw [pk_land hDlt hMlt, pk_land hHlt hMlt, pk_sub]
  · rw [hW, pk_mod_pred, ← hW, Nat.mod_eq_of_lt]
    · refine Finset.sum_congr rfl (fun c hc => ?_)
      have hc' := Finset.mem_range.mp hc
      simp only [hM]
      split_ifs with hle
      · rw [mul_one, hW1 _ (hDlt c hc'), hW1 _ h135]; simp only [hD]; omega
      · simp only [mul_zero, Nat.and_zero]; omega
    · calc _ = ∑ c ∈ Finset.range s, (N c - P c) := by
            refine Finset.sum_congr rfl (fun c hc => ?_)
            have hc' := Finset.mem_range.mp hc
            simp only [hM]
            split_ifs with hle
            · rw [mul_one, hW1 _ (hDlt c hc'), hW1 _ h135]; simp only [hD]; omega
            · simp only [mul_zero, Nat.and_zero]; omega
        _ < W1 := hsum
  · intro c hc
    simp only [hM]
    split_ifs with hle
    · rw [mul_one, hW1 _ (hDlt c hc), hW1 _ h135]; simp only [hD]; omega
    · simp

/-! ## 32-bit slots -/

lemma testBit_get32 (x i b : ℕ) :
    (get32 x i).testBit b = (decide (b < 32) && x.testBit (b + 32 * i)) := by
  simp only [get32, raw_mod, raw_shiftRight, raw_mul]
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow,
    Nat.testBit_div_two_pow]

lemma get32_lt (x i : ℕ) : get32 x i < 2 ^ 32 := by
  simp only [get32, raw_mod]; exact Nat.mod_lt _ (by norm_num)

/-- Decomposition of `x` around slot `i`. -/
lemma decomp32 (x i : ℕ) :
    x = 2 ^ (32 * i) * (2 ^ 32 * (x / 2 ^ (32 * i + 32)) + get32 x i) + x % 2 ^ (32 * i) := by
  have h1 := (Nat.div_add_mod x (2 ^ (32 * i))).symm
  have h2 := (Nat.div_add_mod (x / 2 ^ (32 * i)) (2 ^ 32)).symm
  have h3 : x / 2 ^ (32 * i) / 2 ^ 32 = x / 2 ^ (32 * i + 32) := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  have h4 : get32 x i = x / 2 ^ (32 * i) % 2 ^ 32 := by
    simp only [get32, raw_mod, raw_shiftRight, raw_mul, Nat.shiftRight_eq_div_pow]; norm_num
  rw [h4, ← h3, ← h2]
  exact h1

lemma testBit_slot (lo a hi i m : ℕ) (hlo : lo < 2 ^ (32 * i)) (ha : a < 2 ^ 32) :
    (2 ^ (32 * i) * (2 ^ 32 * hi + a) + lo).testBit m =
      if m < 32 * i then lo.testBit m else if m < 32 * i + 32 then a.testBit (m - 32 * i)
      else hi.testBit (m - 32 * i - 32) := by
  rw [Nat.testBit_two_pow_mul_add _ hlo]
  split_ifs with h1 h2
  · rfl
  · rw [Nat.testBit_two_pow_mul_add _ ha, if_pos (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ ha, if_neg (by omega), Nat.sub_sub]

/-- `set32` replaces slot `i` and leaves the other slots alone. -/
theorem get32_set32 (x i v j : ℕ) (hv : v < 2 ^ 32) :
    get32 (set32 x i v) j = if j = i then v else get32 x j := by
  have hx := decomp32 x i
  have hlo : x % 2 ^ (32 * i) < 2 ^ (32 * i) := Nat.mod_lt _ (by positivity)
  have hset : set32 x i v = 2 ^ (32 * i) * (2 ^ 32 * (x / 2 ^ (32 * i + 32)) + v) + x % 2 ^ (32 * i) := by
    simp only [set32, raw_add, raw_sub, raw_mul, raw_shiftLeft, Nat.shiftLeft_eq]
    conv_lhs => rw [hx]
    have : 2 ^ (32 * i) * (2 ^ 32 * (x / 2 ^ (32 * i + 32)) + get32 x i) + x % 2 ^ (32 * i) -
        get32 x i * 2 ^ (32 * i) = 2 ^ (32 * i) * (2 ^ 32 * (x / 2 ^ (32 * i + 32))) + x % 2 ^ (32 * i) := by
      rw [mul_add, mul_comm (get32 x i)]; omega
    rw [show get32 (2 ^ (32 * i) * (2 ^ 32 * (x / 2 ^ (32 * i + 32)) + get32 x i) + x % 2 ^ (32 * i)) i
      = get32 x i by rw [← hx], this]
    ring
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, testBit_get32, hset, testBit_slot _ _ _ _ _ hlo hv]
    by_cases hb : b < 32
    · rw [if_neg (by omega), if_pos (by omega)]; simp [hb]
    · simp only [hb, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  · rw [if_neg hj, testBit_get32, testBit_get32, hset, testBit_slot _ _ _ _ _ hlo hv]
    conv_rhs => rw [hx]
    rw [testBit_slot _ _ _ _ _ hlo (get32_lt x i)]
    by_cases hb : b < 32
    · simp only [hb, decide_true, Bool.true_and]
      rcases Nat.lt_or_gt_of_ne hj with h | h
      · rw [if_pos (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · simp [hb]

end AutocorrK
