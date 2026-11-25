import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification

/-!
# Lebesgue measure on the unit square is invariant for reflected Brownian motion

For the triangle wave `u = unitIntervalFold` (2-periodic, even, the identity on `[0, 1]`) and a
bounded measurable `ψ`, `∫₀¹ ψ(u(x + w)) dx + ∫₀¹ ψ(u(x - w)) dx = 2 ∫₀¹ ψ`
(`intervalIntegral_unitIntervalFold_add_add_sub`): the two integrals are the integrals of
`ψ ∘ u` over `[w - 1, w]` and `[w, w + 1]`, which together cover one period.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

theorem unitIntervalFold_add_two (z : ℝ) : unitIntervalFold (z + 2) = unitIntervalFold z := by
  have h := unitIntervalFold_sign_mul_sub (Or.inl rfl) (-1) z
  rw [one_mul] at h
  convert h using 2
  push_cast
  ring

theorem unitIntervalFold_neg (z : ℝ) : unitIntervalFold (-z) = unitIntervalFold z := by
  have h := unitIntervalFold_sign_mul_sub (Or.inr rfl) 0 z
  convert h using 2
  push_cast
  ring

theorem unitIntervalFold_of_mem_Icc {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) : unitIntervalFold z = z := by
  unfold unitIntervalFold
  rw [Real.arccos_cos (by nlinarith [Real.pi_pos, hz.1]) (by nlinarith [Real.pi_pos, hz.2])]
  field_simp

theorem unitIntervalFold_of_mem_Icc_one_two {z : ℝ} (hz : z ∈ Icc (1 : ℝ) 2) :
    unitIntervalFold z = 2 - z := by
  have h1 : unitIntervalFold z = unitIntervalFold (z - 2) := by
    rw [← unitIntervalFold_add_two (z - 2), sub_add_cancel]
  rw [h1, ← unitIntervalFold_neg, neg_sub]
  exact unitIntervalFold_of_mem_Icc ⟨by linarith [hz.2], by linarith [hz.1]⟩

/-- **The one-dimensional identity behind the invariance of Lebesgue measure**:
`∫₀¹ ψ(u(x + w)) dx + ∫₀¹ ψ(u(x - w)) dx = 2 ∫₀¹ ψ` for the triangle wave `u` and a bounded
measurable `ψ`. -/
theorem intervalIntegral_unitIntervalFold_add_add_sub {ψ : ℝ → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ y, |ψ y| ≤ C) (w : ℝ) :
    (∫ x in (0 : ℝ)..1, ψ (unitIntervalFold (x + w))) +
        ∫ x in (0 : ℝ)..1, ψ (unitIntervalFold (x - w)) = 2 * ∫ x in (0 : ℝ)..1, ψ x := by
  set φ : ℝ → ℝ := fun z => ψ (unitIntervalFold z) with hφ
  have hφm : Measurable φ := hψ.comp continuous_unitIntervalFold.measurable
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b =>
    (intervalIntegrable_const (c := C)).mono_fun hφm.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        simp only [Real.norm_eq_abs]
        exact (hC _).trans (le_abs_self C))
  have hper : Function.Periodic φ 2 := fun z => by simp only [hφ, unitIntervalFold_add_two]
  have heven : ∀ z, φ (-z) = φ z := fun z => by simp only [hφ, unitIntervalFold_neg]
  have h1 : (∫ x in (0 : ℝ)..1, φ (x + w)) = ∫ x in w..(w + 1), φ x := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm]
  have h2 : (∫ x in (0 : ℝ)..1, φ (x - w)) = ∫ x in (w - 1)..w, φ x := by
    rw [intervalIntegral.integral_comp_sub_right]
    have h : (∫ x in (0 - w)..(1 - w), φ x) = ∫ x in (0 - w)..(1 - w), φ (-x) :=
      intervalIntegral.integral_congr fun x _ => (heven x).symm
    rw [h, intervalIntegral.integral_comp_neg, neg_sub, neg_sub, sub_zero]
  have h3 : (∫ x in (0 : ℝ)..2, φ x) = 2 * ∫ x in (0 : ℝ)..1, ψ x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 2)]
    have ha : (∫ x in (0 : ℝ)..1, φ x) = ∫ x in (0 : ℝ)..1, ψ x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le zero_le_one] at hx
      simp only [hφ, unitIntervalFold_of_mem_Icc hx]
    have hb : (∫ x in (1 : ℝ)..2, φ x) = ∫ x in (0 : ℝ)..1, ψ x := by
      have : (∫ x in (1 : ℝ)..2, φ x) = ∫ x in (1 : ℝ)..2, ψ (2 - x) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le one_le_two] at hx
        simp only [hφ, unitIntervalFold_of_mem_Icc_one_two hx]
      rw [this, intervalIntegral.integral_comp_sub_left]
      norm_num
    rw [ha, hb]
    ring
  simp only [hφ] at h1 h2 h3
  rw [h1, h2, add_comm, intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have h4 := hper.intervalIntegral_add_eq (w - 1) 0
  rw [show w - 1 + 2 = w + 1 by ring, zero_add] at h4
  simp only [hφ] at h4
  rw [h4, h3]

/-- **Invariance in one dimension**: for a bounded measurable `ψ` and every variance `s`,
`∫₀¹ E[ψ(u(x + √s N))] dx = ∫₀¹ ψ`. -/
theorem intervalIntegral_integral_gaussianReal_unitIntervalFold {ψ : ℝ → ℝ} (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) (s : ℝ≥0) :
    ∫ x in (0 : ℝ)..1, ∫ w, ψ (unitIntervalFold w) ∂(gaussianReal x s) =
      ∫ x in (0 : ℝ)..1, ψ x := by
  set N := gaussianReal 0 s with hN
  have hφm : Measurable fun w => ψ (unitIntervalFold w) :=
    hψ.comp continuous_unitIntervalFold.measurable
  have htr : ∀ x : ℝ, ∫ w, ψ (unitIntervalFold w) ∂(gaussianReal x s) =
      ∫ z, ψ (unitIntervalFold (x + z)) ∂N := by
    intro x
    have h : gaussianReal x s = N.map (· + x) := by rw [hN, gaussianReal_map_add_const, zero_add]
    rw [h, integral_map (measurable_add_const x).aemeasurable hφm.aestronglyMeasurable]
    simp only [add_comm]
  simp_rw [htr]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  have hfm : Measurable (Function.uncurry fun (x : ℝ) (z : ℝ) => ψ (unitIntervalFold (x + z))) :=
    hφm.comp measurable_add
  have hint : Integrable (Function.uncurry fun (x : ℝ) (z : ℝ) => ψ (unitIntervalFold (x + z)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod N) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      exact hC _)
  rw [integral_integral_swap hint]
  set G : ℝ → ℝ := fun z => ∫ x in Ioc (0 : ℝ) 1, ψ (unitIntervalFold (x + z)) with hG
  have hGint : Integrable G N := hint.integral_prod_right
  have hNneg : N.map (fun x => -x) = N := by rw [hN, gaussianReal_map_neg, neg_zero]
  have hGneg : Integrable (fun z => G (-z)) N := by
    have h := hGint
    rw [← hNneg] at h
    exact (integrable_map_measure h.aestronglyMeasurable measurable_neg.aemeasurable).1 h
  have hsym : ∫ z, G z ∂N = ∫ z, G (-z) ∂N := by
    conv_lhs => rw [← hNneg]
    rw [integral_map measurable_neg.aemeasurable (by rw [hNneg]; exact hGint.aestronglyMeasurable)]
  have hpair : ∀ z, G z + G (-z) = 2 * ∫ x in Ioc (0 : ℝ) 1, ψ x := by
    intro z
    have h := intervalIntegral_unitIntervalFold_add_add_sub hψ hC z
    simp only [intervalIntegral.integral_of_le zero_le_one] at h ⊢
    exact h
  have h2 : 2 * ∫ z, G z ∂N = 2 * ∫ x in Ioc (0 : ℝ) 1, ψ x := by
    rw [two_mul]
    nth_rewrite 2 [hsym]
    rw [← integral_add hGint hGneg]
    simp_rw [hpair]
    rw [integral_const, probReal_univ, one_smul]
  linarith

/-! ### Two dimensions -/

theorem intervalIntegrable_of_abs_le {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (a b : ℝ) : IntervalIntegrable g volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun hg.aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [Real.norm_eq_abs]
      exact (hC _).trans (le_abs_self C))

theorem measurable_intervalIntegral_param {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (a b : ℝ) : Measurable fun r => ∫ t in a..b, g r t := by
  simp only [intervalIntegral]
  exact ((hg.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc a b))).measurable).sub
    ((hg.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc b a))).measurable)

theorem abs_intervalIntegral_zero_one_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    |∫ t in (0 : ℝ)..1, g t| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (f := g) (C := C)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x)
  rw [Real.norm_eq_abs] at h
  simpa using h

theorem measurable_complex_mk : Measurable fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
  Complex.measurableEquivRealProd.symm.measurable

/-- An integral over the unit square as an iterated interval integral. -/
theorem setIntegral_closedSquare_zero_one_eq {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ z, |f z| ≤ C) :
    ∫ x in closedSquare 0 1, f x = ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1, f ⟨x₁, x₂⟩ := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      closedSquare 0 1 := by
    ext z
    simp only [closedSquare, Complex.mem_reProdIm, Complex.measurableEquivRealProd, mem_preimage,
      mem_prod, Complex.zero_re, Complex.zero_im, zero_add]
    rfl
  have h1 := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  rw [hpre] at h1
  have hfm : Measurable fun p : ℝ × ℝ => f ⟨p.1, p.2⟩ := hf.comp measurable_complex_mk
  have hint : Integrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  calc ∫ x in closedSquare 0 1, f x
      = ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f ⟨p.1, p.2⟩ := h1
    _ = ∫ x₁ in Icc (0 : ℝ) 1, ∫ x₂ in Icc (0 : ℝ) 1, f ⟨x₁, x₂⟩ := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
    _ = ∫ x₁ in (0 : ℝ)..1, ∫ x₂ in (0 : ℝ)..1, f ⟨x₁, x₂⟩ := by
      simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

end HarmonicBalls

