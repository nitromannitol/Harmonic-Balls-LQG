import HarmonicBalls.FirstPass.S8c.Frequency

/-! # The mean of the good indicator over phases and fields (FIRST-PASS fp-S8c-8-2-local, mean step of LocalPhaseTailStep)

If a measurable set `G` of phase-field pairs has, for every phase `θ`, complementary section probability at most `ε`
(the per-phase bound (9), `localPhaseTail_failure_le`, with `ε = ζ/2`), then the product measure of `G` under the
phase probability measure and `P` is at least `1 - ε`, and so is the real integral of its indicator. This is the
mean hypothesis `1 - ζ < ∫ f` of `ae_eventually_frequency_of_birkhoff` (Frequency.lean), at level `ζ/2 < ζ`.
Pure measure theory (Fubini for the product of probability measures).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Product measure of a set from its sections: `1 - ε ≤ (μΘ ⊗ P) G` when every section has complementary
probability at most `ε`. -/
theorem measure_prod_ge_of_sections {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μΘ : Measure Θ) [IsProbabilityMeasure μΘ] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Set (Θ × Ω)} (hG : MeasurableSet G) (ε : ℝ≥0∞)
    (hsec : ∀ θ : Θ, P (Prod.mk θ ⁻¹' G)ᶜ ≤ ε) :
    1 - ε ≤ (μΘ.prod P) G := by
  rw [Measure.prod_apply hG]
  calc 1 - ε = ∫⁻ _ : Θ, 1 - ε ∂μΘ := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ θ, P (Prod.mk θ ⁻¹' G) ∂μΘ := by
      apply lintegral_mono
      intro θ
      have hs : MeasurableSet (Prod.mk θ ⁻¹' G) := hG.preimage measurable_prodMk_left
      have h1 : P (Prod.mk θ ⁻¹' G)ᶜ = 1 - P (Prod.mk θ ⁻¹' G) := prob_compl_eq_one_sub hs
      have h2 : P (Prod.mk θ ⁻¹' G) = 1 - P (Prod.mk θ ⁻¹' G)ᶜ := by
        rw [h1, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
      calc 1 - ε ≤ 1 - P (Prod.mk θ ⁻¹' G)ᶜ := tsub_le_tsub_left (hsec θ) 1
        _ = P (Prod.mk θ ⁻¹' G) := h2.symm

/-- The real integral of the indicator of `G` is at least `1 - ε` under the same hypotheses, for `0 ≤ ε ≤ 1`. -/
theorem integral_indicator_prod_ge {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (μΘ : Measure Θ) [IsProbabilityMeasure μΘ] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Set (Θ × Ω)} (hG : MeasurableSet G) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsec : ∀ θ : Θ, P (Prod.mk θ ⁻¹' G)ᶜ ≤ ENNReal.ofReal ε) :
    1 - ε ≤ ∫ z, G.indicator (1 : Θ × Ω → ℝ) z ∂(μΘ.prod P) := by
  have hmeas := measure_prod_ge_of_sections μΘ P hG (ENNReal.ofReal ε) hsec
  rw [integral_indicator_one hG, measureReal_def]
  have hle : (1 : ℝ≥0∞) - ENNReal.ofReal ε ≤ (μΘ.prod P) G := hmeas
  have hreal : ((1 : ℝ≥0∞) - ENNReal.ofReal ε).toReal = 1 - ε := by
    rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr hε1) ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_ofReal hε0]
  calc 1 - ε = ((1 : ℝ≥0∞) - ENNReal.ofReal ε).toReal := hreal.symm
    _ ≤ ((μΘ.prod P) G).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hle

#print axioms integral_indicator_prod_ge

end HarmonicBalls
