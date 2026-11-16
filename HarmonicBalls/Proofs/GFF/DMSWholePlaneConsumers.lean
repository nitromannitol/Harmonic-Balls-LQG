import HarmonicBalls.Proofs.GFF.DMSWholePlaneUnnormalizedProved
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedComparison

/-!
# First moments of the whole-plane LQG measure

For a whole-plane GFF `(P, hC, hcirc)` and a `γ`-LQG measure `μ` of it with `γ ∈ (0, 2)` and `α₀ = 0`, this file
records the first-moment identities

* `E[μ_h(B_1)] = π`;
* `E[∫ η dμ_h] = ∫ η dz` for every continuous `η ≥ 0` with compact support in the unit ball.

Both follow from the unnormalized whole-plane clause of [DMS, Lemma A.10, p. 184]
(`dmsLemmaA10WholePlaneUnnormalized_holds`), through `HarmonicBalls.integral_measure_ball_eq_pi` and
`HarmonicBalls.integral_lqgMeasure_eq_of_nonneg`. The probability instance on `P` comes from the GFF.

## Main statements

* `HarmonicBalls.IsWholePlaneGFF.integral_measure_ball_eq_pi`
* `HarmonicBalls.IsWholePlaneGFF.integral_lqgMeasure_eq_of_nonneg`
-/

namespace HarmonicBalls

namespace IsWholePlaneGFF

open MeasureTheory Metric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}

/-- `E[μ_h(B_1)] = π` for a `γ`-LQG measure of a whole-plane GFF, `γ ∈ (0, 2)`, `α₀ = 0`. -/
theorem integral_measure_ball_eq_pi (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∫ ω, (μ ω (ball 0 1)).toReal ∂P = Real.pi :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.integral_measure_ball_eq_pi
    (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ) hG hμ

/-- `E[∫ η dμ_h] = ∫ η dz` for a `γ`-LQG measure of a whole-plane GFF, `γ ∈ (0, 2)`, `α₀ = 0`, and every
continuous `η ≥ 0` with compact support contained in the unit ball. -/
theorem integral_lqgMeasure_eq_of_nonneg (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {η : ℂ → ℝ} (hη : Continuous η)
    (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    ∫ ω, ∫ z, η z ∂(μ ω) ∂P = ∫ z, η z :=
  have := hG.isProbabilityMeasure
  HarmonicBalls.integral_lqgMeasure_eq_of_nonneg γ hG hμ
    (dmsLemmaA10WholePlaneUnnormalized_holds P hγ0 hγ2 hC hcirc μ) hη hηs hη0 htsupp

end IsWholePlaneGFF

end HarmonicBalls
