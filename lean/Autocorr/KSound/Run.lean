import Autocorr.KSound.Leaf
import AutocorrK.Stk

/-!
# Soundness of the kernel stack machine and the final kernel theorem

`runK P a b nrec data stk = some stk'` (a segment of the global DFS log) implies that every box of `stk`
is covered once every box of `stk'` is.  A whole certificate starts from the root box and ends with the
empty stack, which gives `HalfClaim n (a/b)`.
-/

namespace AutocorrK

open Autocorr.Cert
open scoped BigOperators

variable {sp : Spec} {P : KP}

def StackOKK (sp : Spec) (lam : ℝ) (stk : List (ℕ × ℕ)) : Prop := ∀ bx ∈ stk, BoxOKK sp lam bx

lemma runK_zero (a b data : ℕ) (stk : List (ℕ × ℕ)) : runK P a b 0 data stk = some stk := rfl

lemma runK_succ (a b nrec data : ℕ) (bx : ℕ × ℕ) (stk : List (ℕ × ℕ)) :
    runK P a b (nrec + 1) data (bx :: stk) =
      sel (Nat.beq (Nat.mod data 4) 0)
        (runK P a b nrec (Nat.shiftRight data 48)
          (propK P (Nat.mod (Nat.shiftRight data 44) 16)
              (set32 bx.1 (Nat.mod (Nat.shiftRight data 2) 128) (Nat.mod (Nat.shiftRight data 9) 2147483648)) bx.2 ::
            propK P (Nat.mod (Nat.shiftRight data 40) 16) bx.1
              (set32 bx.2 (Nat.mod (Nat.shiftRight data 2) 128) (Nat.mod (Nat.shiftRight data 9) 2147483648)) ::
            stk))
        (sel (Nat.beq (Nat.mod data 4) 1)
          (sel (leafOK P a b bx.1 bx.2 (Nat.mod (Nat.shiftRight data 2) 16384)
              (Nat.mod (Nat.shiftRight data 16) (Nat.pow 2 (Nat.mul 87 (Nat.mod (Nat.shiftRight data 2) 16384)))))
            (runK P a b nrec (Nat.shiftRight (Nat.shiftRight data 16) (Nat.mul 87 (Nat.mod (Nat.shiftRight data 2) 16384)))
              stk) none)
          (Option.map (List.cons bx) (runK P a b nrec (Nat.shiftRight data 2) stk))) := rfl

lemma runK_nil (a b nrec data : ℕ) : runK P a b (nrec + 1) data [] = none := rfl

theorem runK_sound (hkp : KPFacts sp P) {a b : ℕ} (hb : 0 < b) (h3 : (a : ℝ) / b ≤ 3) :
    ∀ (nrec data : ℕ) (stk stk' : List (ℕ × ℕ)), runK P a b nrec data stk = some stk' →
      StackOKK sp ((a : ℝ) / b) stk' → StackOKK sp ((a : ℝ) / b) stk := by
  intro nrec
  induction nrec with
  | zero =>
    intro data stk stk' h hok
    rw [runK_zero, Option.some.injEq] at h
    rw [h]; exact hok
  | succ nrec ih =>
    intro data stk stk' h hok
    cases stk with
    | nil => rw [runK_nil] at h; exact absurd h (by simp)
    | cons bx stk =>
      rw [runK_succ] at h
      by_cases hsplit : Nat.mod data 4 = 0
      · rw [beq_true' hsplit, sel_true] at h
        have hall := ih _ _ _ h hok
        intro bx' hbx'
        rcases List.mem_cons.mp hbx' with rfl | hin
        · intro p hp hpb
          have hs : Nat.mod (Nat.shiftRight data 9) 2147483648 < 2 ^ 32 :=
            lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
          rcases child_coverK hkp.wf hp hkp.ints _ _ hs hpb with hc | hc
          · exact hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) p hp hc
          · exact hall _ (List.mem_cons_self ..) p hp hc
        · exact hall bx' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hin))
      · rw [beq_false' hsplit, sel_false] at h
        by_cases hl1 : Nat.mod data 4 = 1
        · rw [beq_true' hl1, sel_true] at h
          by_cases hleaf : leafOK P a b bx.1 bx.2 (Nat.mod (Nat.shiftRight data 2) 16384)
              (Nat.mod (Nat.shiftRight data 16) (Nat.pow 2 (Nat.mul 87 (Nat.mod (Nat.shiftRight data 2) 16384)))) = true
          · rw [hleaf, sel_true] at h
            have hall := ih _ _ _ h hok
            intro bx' hbx'
            rcases List.mem_cons.mp hbx' with rfl | hin
            · exact leafOK_sound hkp hb h3 hleaf
            · exact hall bx' hin
          · rw [Bool.not_eq_true] at hleaf
            rw [hleaf, sel_false] at h
            exact absurd h (by simp)
        · rw [beq_false' hl1, sel_false] at h
          -- delegated: the popped box is in the output
          cases hr : runK P a b nrec (Nat.shiftRight data 2) stk with
          | none => rw [hr] at h; exact absurd h (by simp)
          | some out =>
            rw [hr] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            have hall := ih _ _ _ hr (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
            intro bx' hbx'
            rcases List.mem_cons.mp hbx' with rfl | hin
            · exact hok _ (List.mem_cons_self ..)
            · exact hall bx' hin

lemma stkEq_eq : ∀ (s t : List (ℕ × ℕ)), stkEq s t = true → s = t := by
  intro s
  induction s with
  | nil => intro t h; cases t with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [stkEq])
  | cons x xs ih =>
    intro t h
    cases t with
    | nil => exact absurd h (by simp [stkEq])
    | cons y ys =>
      have h' : sel (Nat.beq x.1 y.1) (sel (Nat.beq x.2 y.2) (stkEq xs ys) false) false = true := h
      by_cases h1 : x.1 = y.1
      · rw [beq_true' h1, sel_true] at h'
        by_cases h2 : x.2 = y.2
        · rw [beq_true' h2, sel_true] at h'
          rw [ih ys h', Prod.ext h1 h2]
        · rw [beq_false' h2, sel_false] at h'; exact absurd h' (by simp)
      · rw [beq_false' h1, sel_false] at h'; exact absurd h' (by simp)

/-- A segment statement. -/
def SegK (sp : Spec) (lam : ℝ) (sin sout : List (ℕ × ℕ)) : Prop :=
  StackOKK sp lam sout → StackOKK sp lam sin

theorem segK_of_check (hkp : KPFacts sp P) {a b : ℕ} (hb : 0 < b) (h3 : (a : ℝ) / b ≤ 3)
    {nrec data : ℕ} {sin sout : List (ℕ × ℕ)} (h : segCheck P a b nrec data sin sout = true) :
    SegK sp ((a : ℝ) / b) sin sout := by
  unfold segCheck at h
  cases hr : runK P a b nrec data sin with
  | none => rw [hr] at h; exact absurd h (by simp)
  | some s =>
    rw [hr] at h
    have := stkEq_eq s sout h
    subst this
    exact runK_sound hkp hb h3 nrec data sin s hr

lemma SegK.trans {lam : ℝ} {s1 s2 s3 : List (ℕ × ℕ)} (h1 : SegK sp lam s1 s2) (h2 : SegK sp lam s2 s3) :
    SegK sp lam s1 s3 := fun h => h1 (h2 h)

/-- Frame: extra output boxes on the front. -/
lemma SegK.frame {lam : ℝ} {sin sout : List (ℕ × ℕ)} (D : List (ℕ × ℕ)) (h : SegK sp lam sin sout) :
    SegK sp lam sin (D ++ sout) := fun hD => h (fun bx hbx => hD bx (List.mem_append_right _ hbx))

lemma SegK.prefix {lam : ℝ} {sin sout : List (ℕ × ℕ)} (D : List (ℕ × ℕ)) (h : SegK sp lam sin sout) :
    SegK sp lam (D ++ sin) (D ++ sout) := by
  intro hD bx hbx
  rcases List.mem_append.mp hbx with h1 | h1
  · exact hD bx (List.mem_append_left _ h1)
  · exact h (fun b hb => hD b (List.mem_append_right _ hb)) bx h1

/-! Assembly of the per-segment statements (used by the generated modules). -/

lemma StackOKK.nil {lam : ℝ} : StackOKK sp lam [] := fun _ h => absurd h List.not_mem_nil

lemma StackOKK.cons {lam : ℝ} {x : ℕ × ℕ} {xs : List (ℕ × ℕ)} (h : BoxOKK sp lam x)
    (t : StackOKK sp lam xs) : StackOKK sp lam (x :: xs) := by
  intro bx hbx
  rcases List.mem_cons.mp hbx with rfl | hin
  · exact h
  · exact t bx hin

lemma StackOKK.append {lam : ℝ} {xs ys : List (ℕ × ℕ)} (h1 : StackOKK sp lam xs)
    (h2 : StackOKK sp lam ys) : StackOKK sp lam (xs ++ ys) := by
  intro bx hbx
  rcases List.mem_append.mp hbx with h | h
  · exact h1 bx h
  · exact h2 bx h

/-- A segment whose output is `D ++ sout`, with `D` (delegated boxes) and `sout` covered. -/
lemma StackOKK.of_seg {lam : ℝ} {sin D sout : List (ℕ × ℕ)} (h : SegK sp lam sin (D ++ sout))
    (hD : StackOKK sp lam D) (hs : StackOKK sp lam sout) : StackOKK sp lam sin :=
  h (hD.append hs)

lemma StackOKK.head {lam : ℝ} {x : ℕ × ℕ} (h : StackOKK sp lam [x]) : BoxOKK sp lam x :=
  h x (List.mem_singleton_self x)

/-- Soundness of the core-only composition `StkK` used by the generated modules. -/
theorem stkK_sound (hkp : KPFacts sp P) {a b : ℕ} (hb : 0 < b) (h3 : (a : ℝ) / b ≤ 3)
    {stk : List (ℕ × ℕ)} (h : StkK P a b stk) : StackOKK sp ((a : ℝ) / b) stk := by
  induction h with
  | nil => exact StackOKK.nil
  | cons _ _ ih1 ih2 => exact StackOKK.cons ih1.head ih2
  | seg nrec data hc _ ih => exact segK_of_check hkp hb h3 hc ih

/-- The starting box of the root: `L = 0`, `U = 1` in every slot. -/
lemma inbox_trivial {p : ℕ → ℝ} (hp : Adm sp p) {up : ℕ}
    (hup : ∀ b < sp.nB, get32 up b = 2 ^ 30) : InBoxK sp p 0 up := by
  intro b hb
  constructor
  · simp [get32, raw_mod, raw_shiftRight, mass_nonneg hp b]
  · rw [hup b hb]
    have := mass_le_one hp b
    norm_num
    exact this

/-- Covering the kernel root box is the half-space claim. -/
theorem halfClaim_of_rootK (hkp : KPFacts sp P) {up k : ℕ} (hup : ∀ b < sp.nB, get32 up b = 2 ^ 30)
    {lam : ℝ} (hok : BoxOKK sp lam (propK P k 0 up)) : Autocorr.HalfClaim sp.n lam := by
  intro q hq hsum hhalf
  set p : ℕ → ℝ := fun i => if h : i < sp.n then q ⟨i, h⟩ else 0 with hpdef
  have hpq : ∀ i : Fin sp.n, p i = q i := fun i => by simp [hpdef, i.isLt]
  have hsumR : ∀ f : ℕ → ℝ, ∑ i : Fin sp.n, f i = ∑ i ∈ Finset.range sp.n, f i :=
    fun f => Fin.sum_univ_eq_sum_range f sp.n
  have hp : Adm sp p := by
    refine ⟨fun i => ?_, fun i hi => ?_, ?_, ?_⟩
    · simp only [hpdef]; split_ifs
      · exact hq _
      · exact le_refl 0
    · simp only [hpdef]; rw [dif_neg (by omega)]
    · rw [← hsumR p, ← hsum]
      exact Finset.sum_congr rfl (fun i _ => hpq i)
    · rw [← hsumR (fun i => (2 * (i : ℝ) - ((sp.n : ℝ) - 1)) * p i)]
      calc ∑ i : Fin sp.n, (2 * ((i : ℕ) : ℝ) - ((sp.n : ℝ) - 1)) * p i
          = ∑ i : Fin sp.n, (2 * ((i : ℕ) : ℝ) - ((sp.n : ℝ) - 1)) * q i :=
            Finset.sum_congr rfl (fun i _ => by rw [hpq i])
        _ ≤ 0 := hhalf
  have hin := propK_sound hkp.wf hp hkp.ints k (inbox_trivial hp hup)
  obtain ⟨c1, c2, h12, h2, hineq⟩ := hok p hp hin
  refine ⟨c1, c2, h12, h2, ?_⟩
  have hws : wsum sp p c1 c2 = Autocorr.winSum q c1 c2 := by
    unfold wsum Autocorr.winSum
    rw [← hsumR]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hsumR (fun j => if c1 ≤ (i : ℕ) + j ∧ (i : ℕ) + j ≤ c2 then p i * p j else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hpq i, hpq j]
  rw [← hws]
  exact hineq

end AutocorrK
