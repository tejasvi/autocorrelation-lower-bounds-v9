import C64.Settle

/-!
# Pinned sets with lists of pins (the form used by the checker)

The same statements as Lemmas 6.4(a), 6.4(b) and the witness homotopy of `C64.Settle`, with the pinned points,
their boxes and multipliers given as lists (as in the checker's data) instead of `Fin k`-indexed families.
-/

open MeasureTheory Set Complex Real ComplexConjugate

namespace C64

/-- `μ` lies in the pinned set `𝒫(τ', z_c, r'; (p, Q) ∈ pq)`. -/
def PinnedL (τ' : ℝ) (zc : ℂ) (r' : ℝ) (pq : List (ℂ × Box)) (μ : Measure ℝ) : Prop :=
  ClassA τ' μ ∧ (∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r') ∧ ∀ x ∈ pq, x.2.mem (hat μ x.1)

lemma PinnedL.mono {τ τ' r r' : ℝ} {zc : ℂ} {pq : List (ℂ × Box)} {μ : Measure ℝ}
    (h : PinnedL τ zc r pq μ) (hτ : τ ≤ τ') (hr : r ≤ r') : PinnedL τ' zc r' pq μ :=
  ⟨h.1.mono hτ, let ⟨σ, h1, h2⟩ := h.2.1; ⟨σ, h1, h2.trans hr⟩, h.2.2⟩

/-- A pin of a leaf: the point `p`, its box `Q`, a multiplier `y`, and bounds `lo ≤ Re(ȳ x) ≤ hi` on `Q`. -/
structure PinD where
  p : ℂ
  Q : Box
  y : ℂ
  lo : ℝ
  hi : ℝ

/-- `Λ(t) = Re(v̄ K_t(z_c)) + Σ Re(ȳ K_t(p))`. -/
noncomputable def LamL (v zc : ℂ) (ds : List PinD) (t : ℝ) : ℝ :=
  (conj v * Kt t zc).re + (ds.map fun d => (conj d.y * Kt t d.p).re).sum

lemma continuous_LamL (v zc : ℂ) (ds : List PinD) : Continuous (LamL v zc ds) := by
  unfold LamL
  refine (continuous_re_conj_mul_Kt v zc).add ?_
  induction ds with
  | nil => simp only [List.map_nil, List.sum_nil]; exact continuous_const
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_re_conj_mul_Kt d.y d.p).add ih

lemma integrable_sumL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (ds : List PinD) :
    Integrable (fun t => (ds.map fun d => (conj d.y * Kt t d.p).re).sum) μ := by
  induction ds with
  | nil => have := hμ.1; simp only [List.map_nil, List.sum_nil]; exact integrable_const (0 : ℝ)
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (integrable_re_conj_mul_Kt hμ d.y d.p).add ih

lemma integral_sumL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (ds : List PinD) :
    ∫ t, (ds.map fun d => (conj d.y * Kt t d.p).re).sum ∂μ = (ds.map fun d => (conj d.y * hat μ d.p).re).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (integrable_re_conj_mul_Kt hμ d.y d.p) (integrable_sumL hμ ds), ih, re_conj_mul_hat hμ]

lemma integrable_LamL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (v zc : ℂ) (ds : List PinD) :
    Integrable (LamL v zc ds) μ :=
  (integrable_re_conj_mul_Kt hμ v zc).add (integrable_sumL hμ ds)

lemma integral_LamL {τ : ℝ} {μ : Measure ℝ} (hμ : ClassA τ μ) (v zc : ℂ) (ds : List PinD) :
    ∫ t, LamL v zc ds t ∂μ = (conj v * hat μ zc).re + (ds.map fun d => (conj d.y * hat μ d.p).re).sum := by
  unfold LamL
  rw [integral_add (integrable_re_conj_mul_Kt hμ v zc) (integrable_sumL hμ ds), integral_sumL hμ, re_conj_mul_hat hμ]

/-- The boxes of the pins. -/
def pqOf (ds : List PinD) : List (ℂ × Box) := ds.map fun d => (d.p, d.Q)

lemma sum_lo_le {μ : Measure ℝ} {ds : List PinD} (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi)
    (hQ : ∀ x ∈ pqOf ds, x.2.mem (hat μ x.1)) :
    (ds.map fun d => d.lo).sum ≤ (ds.map fun d => (conj d.y * hat μ d.p).re).sum := by
  refine List.sum_le_sum (fun d hd => (hbox d hd _ (hQ (d.p, d.Q) (List.mem_map.2 ⟨d, hd, rfl⟩))).1)

lemma sum_le_hi {μ : Measure ℝ} {ds : List PinD} (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi)
    (hQ : ∀ x ∈ pqOf ds, x.2.mem (hat μ x.1)) :
    (ds.map fun d => (conj d.y * hat μ d.p).re).sum ≤ (ds.map fun d => d.hi).sum := by
  refine List.sum_le_sum (fun d hd => (hbox d hd _ (hQ (d.p, d.Q) (List.mem_map.2 ⟨d, hd, rfl⟩))).2)

/-- Lemma 6.4(a) (exclusion) with lists of pins. -/
theorem pinnedL_empty {τ : ℝ} (hτ : 0 ≤ τ) {zc : ℂ} {r : ℝ} {ds : List PinD} {v : ℂ}
    (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi) (hX : 0 ≤ (conj v * S zc).re)
    (hE : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * LamL v zc ds t < (conj v * S zc).re - ‖v‖ * r + (ds.map fun d => d.lo).sum)
    (hEpos : 0 < (conj v * S zc).re - ‖v‖ * r + (ds.map fun d => d.lo).sum)
    {μ : Measure ℝ} (hμ : PinnedL τ zc r (pqOf ds) μ) : False := by
  obtain ⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩ := hμ
  set E := (conj v * S zc).re - ‖v‖ * r + (ds.map fun d => d.lo).sum
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc (continuous_LamL v zc ds)
  set B := max 0 (LamL v zc ds t₀)
  have hB0 : 0 ≤ B := le_max_left _ _
  have hint := integral_le_of_classA hA hτ (integrable_LamL hA v zc ds) hB0
    (fun t ht => (hmax t ht).trans (le_max_right _ _))
  have hτB : τ * B < E := by
    rcases le_total (LamL v zc ds t₀) 0 with h | h
    · rw [show B = 0 from max_eq_left h, mul_zero]; exact hEpos
    · rw [show B = LamL v zc ds t₀ from max_eq_right h]; exact hE t₀ ht₀
  have hlow : E ≤ ∫ t, LamL v zc ds t ∂μ := by
    rw [integral_LamL hA]
    have h1 := re_conj_mul_ge v (S zc) (hat μ zc) σ hσr
    have h2 : (σ : ℝ) * (conj v * S zc).re ≥ (conj v * S zc).re := by nlinarith
    have h3 := sum_lo_le hbox hQ
    simp only [E]; linarith
  linarith

/-- Lemma 6.4(b) for convex combinations of two pinned measures, with lists of pins. -/
theorem pinnedL_tile_ne {τ' : ℝ} (hτ : 0 ≤ τ') {zc : ℂ} {r' : ℝ} {ds : List PinD} {u v : ℂ}
    (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi) {p : ℂ} (hX : (conj v * S zc).re ≤ 0)
    (hW : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ' * ((conj u * Kt t p).re - LamL v zc ds t) <
      (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum)
    (hWpos : 0 < (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum)
    {μ ν : Measure ℝ} (hμ : PinnedL τ' zc r' (pqOf ds) μ) (hν : PinnedL τ' zc r' (pqOf ds) ν)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) : S p - ((1 - θ) * hat μ p + θ * hat ν p) ≠ 0 := by
  set W := (conj u * S p).re - (conj v * S zc).re - ‖v‖ * r' - (ds.map fun d => d.hi).sum
  set φ : ℝ → ℝ := fun t => (conj u * Kt t p).re - LamL v zc ds t with hφ
  have hφc : Continuous φ := (continuous_re_conj_mul_Kt u p).sub (continuous_LamL v zc ds)
  obtain ⟨t₀, ht₀, hmax⟩ := exists_max_on_Icc hφc
  set B := max 0 (φ t₀)
  have hB0 : 0 ≤ B := le_max_left _ _
  have hτB : τ' * B < W := by
    rcases le_total (φ t₀) 0 with h | h
    · rw [show B = 0 from max_eq_left h, mul_zero]; exact hWpos
    · rw [show B = φ t₀ from max_eq_right h]; exact hW t₀ ht₀
  have key : ∀ ρ : Measure ℝ, PinnedL τ' zc r' (pqOf ds) ρ →
      (conj u * hat ρ p).re ≤ τ' * B + ((conj v * S zc).re + ‖v‖ * r' + (ds.map fun d => d.hi).sum) := by
    intro ρ ⟨hA, ⟨σ, hσ1, hσr⟩, hQ⟩
    have hint := integral_le_of_classA hA hτ (φ := fun t => (conj u * Kt t p).re - LamL v zc ds t)
      ((integrable_re_conj_mul_Kt hA u p).sub (integrable_LamL hA v zc ds))
      hB0 (fun t ht => (hmax t ht).trans (le_max_right _ _))
    rw [integral_sub (integrable_re_conj_mul_Kt hA u p) (integrable_LamL hA v zc ds), ← re_conj_mul_hat hA,
      integral_LamL hA] at hint
    have h1 := re_conj_mul_le v (S zc) (hat ρ zc) σ hσr
    have h2 : (σ : ℝ) * (conj v * S zc).re ≤ (conj v * S zc).re := by nlinarith
    have h3 := sum_le_hi hbox hQ
    linarith
  intro h0
  have hSp : S p = (1 - θ) * hat μ p + θ * hat ν p := sub_eq_zero.1 h0
  have hre : (conj u * S p).re = (1 - θ) * (conj u * hat μ p).re + θ * (conj u * hat ν p).re := by
    rw [hSp]
    simp only [mul_add, Complex.add_re]
    rw [show conj u * ((1 - (θ : ℂ)) * hat μ p) = ((1 - θ : ℝ) : ℂ) * (conj u * hat μ p) by push_cast; ring,
      show conj u * ((θ : ℂ) * hat ν p) = (θ : ℂ) * (conj u * hat ν p) by ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hk1 := key μ hμ
  have hk2 := key ν hν
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have : (conj u * S p).re ≤ τ' * B + ((conj v * S zc).re + ‖v‖ * r' + (ds.map fun d => d.hi).sum) := by
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hk1 hθ1, mul_le_mul_of_nonneg_left hk2 hθ0]
  simp only [W] at hτB
  linarith

/-- Every measure pinned in the leaf has an odd-winding ellipse. -/
def LeafSettledL (τ : ℝ) (zc : ℂ) (r : ℝ) (pq : List (ℂ × Box)) : Prop :=
  ∀ μ : Measure ℝ, PinnedL τ zc r pq μ → OddLoop μ

theorem leafSettledL_of_exclusion {τ : ℝ} (hτ : 0 ≤ τ) {zc : ℂ} {r : ℝ} {ds : List PinD} {v : ℂ}
    (hbox : ∀ d ∈ ds, BoxBounds d.y d.Q d.lo d.hi) (hX : 0 ≤ (conj v * S zc).re)
    (hE : ∀ t ∈ Icc (-1/2 : ℝ) (1/2), τ * LamL v zc ds t < (conj v * S zc).re - ‖v‖ * r + (ds.map fun d => d.lo).sum)
    (hEpos : 0 < (conj v * S zc).re - ‖v‖ * r + (ds.map fun d => d.lo).sum) : LeafSettledL τ zc r (pqOf ds) :=
  fun _ hμ => (pinnedL_empty hτ hbox hX hE hEpos hμ).elim

/-- The witness homotopy with lists of pins. -/
theorem leafSettledL_of_witness {τ τ' r r' : ℝ} (hττ' : τ ≤ τ') (hrr' : r ≤ r') {zc : ℂ}
    {pq : List (ℂ × Box)} {cT : ℂ} {aT bT : ℝ} (haT : 0 < aT) (hbT : 0 < bT)
    (htile : ∀ q ∈ Icc (0 : ℝ) 1, ∀ μ ν : Measure ℝ, PinnedL τ' zc r' pq μ → PinnedL τ' zc r' pq ν →
      ∀ θ ∈ Icc (0 : ℝ) 1, S (ellipse cT aT bT q) -
        ((1 - θ) * hat μ (ellipse cT aT bT q) + θ * hat ν (ellipse cT aT bT q)) ≠ 0)
    {ν : Measure ℝ} (hν : PinnedL τ' zc r' pq ν) {n : ℤ} (hn : Odd n)
    (hwind : HasWinding (fun q => G ν (ellipse cT aT bT q)) n) : LeafSettledL τ zc r pq := by
  intro μ hμ
  have hμ' := hμ.mono hττ' hrr'
  set H : ℝ → ℝ → ℂ := fun θ q => S (ellipse cT aT bT q) -
    (θ * hat μ (ellipse cT aT bT q) + (1 - θ) * hat ν (ellipse cT aT bT q)) with hH
  have hne : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ q ∈ Icc (0 : ℝ) 1, H θ q ≠ 0 := by
    intro θ hθ q hq
    have := htile q hq μ ν hμ' hν (1 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    simpa [hH, sub_sub_cancel, add_comm] using this
  have hcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
    apply Continuous.continuousOn
    have h1 : Continuous fun p : ℝ × ℝ => ellipse cT aT bT p.2 := (continuous_ellipse cT aT bT).comp continuous_snd
    have hμc := continuous_hat_of_classA hμ'.1
    have hνc := continuous_hat_of_classA hν.1
    exact (continuous_S.comp h1).sub (((Complex.continuous_ofReal.comp continuous_fst).mul (hμc.comp h1)).add
      ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul (hνc.comp h1)))
  have hper : ∀ θ ∈ Icc (0 : ℝ) 1, H θ 0 = H θ 1 := fun θ _ => by simp only [hH, ellipse_zero_eq_one]
  have h0 : HasWinding (H 0) n := by
    have : H 0 = fun q => G ν (ellipse cT aT bT q) := by funext q; simp [hH, G]
    rw [this]; exact hwind
  have h1 := hasWinding_homotopy hcont hne hper h0
  refine ⟨cT, aT, bT, haT, hbT, fun q hq => ?_, n, hn, ?_⟩
  · have := hne 1 ⟨zero_le_one, le_rfl⟩ q hq; simpa [hH, G] using this
  · have : H 1 = fun q => G μ (ellipse cT aT bT q) := by funext q; simp [hH, G]
    rw [← this]; exact h1

/-- An arc of type H with list-indexed pins. -/
theorem settled_HL {τ c a b s₀ s₁ : ℝ} {zc : ℂ} {r : ℝ}
    (hloc : ∀ μ : Measure ℝ, ClassA τ μ → ∀ s ∈ Icc s₀ s₁, ∀ lam ∈ Ioc (0 : ℝ) 1,
      S (ellipse c a b s) = lam * hat μ (ellipse c a b s) → ∃ σ : ℝ, 1 ≤ σ ∧ ‖hat μ zc - (σ : ℂ) * S zc‖ ≤ r)
    (hcov : ∀ μ : Measure ℝ, ClassA τ μ → ∃ pq : List (ℂ × Box), (∀ x ∈ pq, x.2.mem (hat μ x.1)) ∧
      LeafSettledL τ zc r pq) :
    ArcSettled τ c a b s₀ s₁ := by
  intro μ hμ s hs lam hlam hcr
  obtain ⟨σ, hσ1, hσr⟩ := hloc μ hμ s hs lam hlam hcr
  obtain ⟨pq, hQ, hset⟩ := hcov μ hμ
  exact hset μ ⟨hμ, ⟨σ, hσ1, hσr⟩, hQ⟩

end C64
