import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive

/-! # Stationarity at positive good-annulus thresholds -/

open MeasureTheory ProbabilityTheory Metric MarkovProcess
open scoped NNReal

namespace HarmonicBalls

open Classical in
/-- Point avoidance and the staged field/measure invariance inputs give
stationarity of the joint indicators at positive good-annulus thresholds. -/
theorem identDistrib_lqg_veryGoodComparable_of_ae_point_avoidance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_unit_good hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m
  apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha
  simpa using hpolar

end HarmonicBalls
