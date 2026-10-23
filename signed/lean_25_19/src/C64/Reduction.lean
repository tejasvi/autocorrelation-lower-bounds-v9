import C64.Winding
import C64.Fourier

/-!
# The reduction (paper Proposition 6.7 and Corollary 6.8, one-sided case, in arc form)

`arcReduction : ArcReduction`: if `S` winds an odd number of times along `T₁` and settled arcs cover `[0, 1]`, then
`ess sup (f ⋆ f) > (∫ f)² / (1 - τ)` for every admissible `f` with `∫ f ≠ 0`.

Proof.  Normalize `∫ f = 1` and suppose `M ≤ 1/(1 - τ)`.  The measure `w = 1_{[-1/2,1/2]} - (f ⋆ f)/M` lies in
`𝒜_τ` and `G_w = F²/M`, so along every closed ellipse on which `G_w` does not vanish its winding number is even
(`hasWinding_even_of_sq`).  If no `G_{λw}` (`0 ≤ λ ≤ 1`) vanished on `T₁`, the homotopy `λ ↦ G_{λw}` would carry
the odd winding number of `S` to `G_w`; so `w` has a crossing on `T₁`, the arc containing it is settled, and `w` has
an odd-winding ellipse: a contradiction.
-/

open MeasureTheory Set Complex Real Filter Topology

namespace C64

lemma continuous_ellipse (c : ℂ) (a b : ℝ) : Continuous (ellipse c a b) := by
  unfold ellipse; fun_prop

lemma ellipse_zero_eq_one (c : ℂ) (a b : ℝ) : ellipse c a b 0 = ellipse c a b 1 := by
  simp [ellipse]

/-- The restriction of Lebesgue measure to `[-1/2, 1/2]`. -/
noncomputable def lebI : Measure ℝ := volume.restrict (Icc (-1/2 : ℝ) (1/2))

instance : IsFiniteMeasure lebI := by
  unfold lebI; exact isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])

lemma S_eq_hat_lebI (z : ℂ) : S z = hat lebI z := by
  rw [S_eq_integral, hat, lebI, intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]

lemma continuous_S : Continuous S := by
  have : S = hat lebI := funext S_eq_hat_lebI
  rw [this]
  exact continuous_hat (by simp [lebI, Measure.restrict_apply' measurableSet_Icc])

lemma ClassA.mono {τ τ' : ℝ} {μ : Measure ℝ} (h : ClassA τ μ) (hττ' : τ ≤ τ') : ClassA τ' μ :=
  ⟨h.1, h.2.1, h.2.2.trans (ENNReal.ofReal_le_ofReal hττ')⟩

lemma continuous_hat_of_classA {τ : ℝ} {μ : Measure ℝ} (h : ClassA τ μ) : Continuous (hat μ) := by
  have := h.1
  exact continuous_hat h.2.1

/-- Arcs that chain from `x₀` to `1` cover `[x₀, 1]`. -/
lemma CoversUnit.cover : ∀ (arcs : List (ℝ × ℝ)) (x₀ : ℝ), (∀ p ∈ arcs.head?, p.1 = x₀) → CoversUnit arcs →
    ∀ s, x₀ ≤ s → s ≤ 1 → ∃ p ∈ arcs, p.1 ≤ s ∧ s ≤ p.2
  | [], _, _, h, _, _, _ => absurd h (by simp [CoversUnit])
  | [p], x₀, hh, h, s, hs0, hs1 => by
    have hp1 : p.1 = x₀ := hh p (by simp)
    have hp2 : p.2 = 1 := h
    exact ⟨p, by simp, by rw [hp1]; exact hs0, by rw [hp2]; exact hs1⟩
  | p :: q :: rest, x₀, hh, h, s, hs0, hs1 => by
    have hp1 : p.1 = x₀ := hh p (by simp)
    obtain ⟨hpq, hrest⟩ := h
    by_cases hsp : s ≤ p.2
    · exact ⟨p, by simp, by rw [hp1]; exact hs0, hsp⟩
    · obtain ⟨r, hr, hr1, hr2⟩ := CoversUnit.cover (q :: rest) q.1 (by simp) hrest s
        (by rw [← hpq]; exact (not_le.1 hsp).le) hs1
      exact ⟨r, List.mem_cons_of_mem _ hr, hr1, hr2⟩

/-- The normalized case `∫ f = 1` of the reduction. -/
theorem arcReduction_normalized {τ c a b : ℝ} (hτ1 : τ < 1) (ha : 0 < a) (hb : 0 < b)
    (hS0 : ∀ s ∈ Icc (0 : ℝ) 1, S (ellipse c a b s) ≠ 0)
    (hSwind : ∃ n : ℤ, Odd n ∧ HasWinding (fun s => S (ellipse c a b s)) n)
    (arcs : List (ℝ × ℝ)) (hhead : ∀ p ∈ arcs.head?, p.1 = 0) (hcov : CoversUnit arcs)
    (hset : ∀ p ∈ arcs, ArcSettled τ c a b p.1 p.2)
    {f : ℝ → ℝ} (hf : Admissible f) (hint : ∫ x, f x = 1) {M : ℝ}
    (hM : ∀ᵐ t ∂(volume : Measure ℝ), autoconv f t ≤ M) : 1 / (1 - τ) < M := by
  by_contra hle
  push Not at hle
  have hMpos := M_pos hf hint hM
  have hτM : 1 - 1 / M ≤ τ := by
    have h1 : 0 < 1 - τ := by linarith
    rw [le_div_iff₀ h1] at hle
    have h2 : 1 - τ ≤ 1 / M := by rw [le_div_iff₀ hMpos]; linarith
    linarith
  set μ := wmeas f M with hμdef
  have hA : ClassA τ μ := (classA_wmeas hf hint hM).mono hτM
  have hG : ∀ z, G μ z = (1 / M : ℂ) * FT f z ^ 2 := fun z => by
    rw [G_wmeas hf hint hM]; ring
  -- every closed ellipse on which `G_μ` does not vanish has even winding number
  have heven : ¬ OddLoop μ := by
    rintro ⟨c', a', b', _, _, hne, n, hodd, hwind⟩
    have hF0 : ∀ s ∈ Icc (0 : ℝ) 1, FT f (ellipse c' a' b' s) ≠ 0 := by
      intro s hs h0; apply hne s hs; rw [hG, h0]; ring
    have := hasWinding_even_of_sq ((continuous_FT hf).comp (continuous_ellipse c' a' b')).continuousOn hF0
      (by simp only [Function.comp, ellipse_zero_eq_one]) (by simp [hMpos.ne'])
      (fun s _ => hG (ellipse c' a' b' s)) hwind
    exact (Int.not_even_iff_odd.2 hodd) this
  -- a crossing on T₁
  obtain ⟨n, hodd, hwind⟩ := hSwind
  have hcross : ∃ s ∈ Icc (0 : ℝ) 1, ∃ lam ∈ Ioc (0 : ℝ) 1,
      S (ellipse c a b s) = lam * hat μ (ellipse c a b s) := by
    by_contra hno
    push Not at hno
    -- no G_{λμ} vanishes on T₁
    have hne : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        S (ellipse c a b s) - lam * hat μ (ellipse c a b s) ≠ 0 := by
      intro lam hlam s hs h0
      rcases eq_or_lt_of_le hlam.1 with h | h
      · subst h; apply hS0 s hs; simpa using h0
      · exact hno s hs lam ⟨h, hlam.2⟩ (by linear_combination h0)
    set H : ℝ → ℝ → ℂ := fun lam s => S (ellipse c a b s) - lam * hat μ (ellipse c a b s)
    have hHc : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc 0 1) := by
      apply Continuous.continuousOn
      have h1 : Continuous fun p : ℝ × ℝ => ellipse c a b p.2 := (continuous_ellipse c a b).comp continuous_snd
      exact (continuous_S.comp h1).sub ((Complex.continuous_ofReal.comp continuous_fst).mul
        ((continuous_hat_of_classA hA).comp h1))
    have hH0 : HasWinding (H 0) n := by
      have : H 0 = fun s => S (ellipse c a b s) := by funext s; simp [H]
      rw [this]; exact hwind
    have hH1 := hasWinding_homotopy hHc hne (fun lam _ => by simp only [H, ellipse_zero_eq_one]) hH0
    apply heven
    refine ⟨c, a, b, ha, hb, ?_, n, hodd, ?_⟩
    · intro s hs; have := hne 1 ⟨zero_le_one, le_rfl⟩ s hs; simpa [G, H] using this
    · have : H 1 = fun s => G μ (ellipse c a b s) := by funext s; simp [H, G]
      rw [← this]; exact hH1
  obtain ⟨s, hs, lam, hlam, hcr⟩ := hcross
  obtain ⟨p, hp, hp1, hp2⟩ := CoversUnit.cover arcs 0 hhead hcov s hs.1 hs.2
  exact heven (hset p hp μ hA s ⟨hp1, hp2⟩ lam hlam hcr)

lemma admissible_div {f : ℝ → ℝ} (hf : Admissible f) (c : ℝ) : Admissible (fun x => f x / c) := by
  refine ⟨hf.1.div_const c, ?_⟩
  filter_upwards [hf.2] with x hx hxI
  simp [hx hxI]

lemma autoconv_div (f : ℝ → ℝ) (c : ℝ) : autoconv (fun x => f x / c) = fun t => autoconv f t / c ^ 2 := by
  funext t
  simp only [autoconv, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_div]
  congr 1; funext s; ring

/-- Proposition 6.7 + Corollary 6.8 (one-sided case) in arc form. -/
theorem arcReduction : ArcReduction := by
  intro τ c a b _ hτ1 ha hb hS0 hSwind arcs hhead hcov hset f hf hint M hM
  set I := ∫ x, f x with hIdef
  have hI2 : 0 < I ^ 2 := by positivity
  have hf₁ := admissible_div hf I
  have hint₁ : ∫ x, f x / I = 1 := by rw [integral_div, ← hIdef, div_self hint]
  have hM₁ : ∀ᵐ t ∂(volume : Measure ℝ), autoconv (fun x => f x / I) t ≤ M / I ^ 2 := by
    rw [autoconv_div]
    filter_upwards [hM] with t ht
    exact div_le_div_of_nonneg_right ht hI2.le
  have h := arcReduction_normalized hτ1 ha hb hS0 hSwind arcs hhead hcov hset hf₁ hint₁ hM₁
  rw [lt_div_iff₀ hI2] at h
  have h1 : 0 < 1 - τ := by linarith
  calc I ^ 2 / (1 - τ) = 1 / (1 - τ) * I ^ 2 := by ring
    _ < M := h

end C64
