import HarmonicBalls.Proofs.Sec8.LocalMeasureExtension

/-! # Almost-everywhere local normalized measure representatives -/

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

open Classical MarkovProcess in
/-- Almost-sure germ-measurable versions of normalized restrictions provide
local good-scale indicator versions. -/
theorem ae_local_veryGoodComparable_indicators_of_ae_normalizedRestriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (βminus : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  apply ae_local_veryGoodComparable_indicators_of_local_finite_measures P germ μ βminus N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hfull
  intro ε hε
  obtain ⟨ν, hν, heq⟩ := hrep ε hε
  refine ⟨ν, hν, ?_, ?_⟩
  · filter_upwards [heq, hatom] with ω hω hωatom
    rw [hω]
    refine ⟨?_, inferInstance⟩
    intro x
    have hz : μ ω ({x} ∩ ball 0 ε) = 0 := measure_mono_null inter_subset_left (hωatom x)
    simp [normalizedRestriction, Measure.smul_apply,
      Measure.restrict_apply (measurableSet_singleton x), hz]
  · filter_upwards [heq, ae_referenceBall_pos_finite P μ hfull hloc] with ω hω hpos
    refine ⟨μ ω (ball 0 ε), (hpos ε hε).1, (hpos ε hε).2, ?_⟩
    rw [hω]
    exact restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet
      (hpos ε hε).1 (hpos ε hε).2

end HarmonicBalls
