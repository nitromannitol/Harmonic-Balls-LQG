import HarmonicBalls.Proofs.Sec6.StoppedSubharmonicApproximation
import HarmonicBalls.Proofs.Sec6.SubmartingaleHarmonicMeasure

/-! # Harmonic measure bounds from generator-subharmonic approximation -/

namespace HarmonicBalls.Section6

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty

/-- Uniform approximation by functions with nonnegative generator gives the
harmonic-measure boundary estimate. -/
theorem ofReal_le_boundary_mul_harmonicMeasure_of_generator_approximation
    {A Y : Set ℂ} (hA : IsOpen A) (hY : IsOpen Y) (hAb : Bornology.IsBounded A)
    (hYA : Y ⊆ A) {q : ℂ → ℝ} (hqmeas : Measurable q)
    (hqnonneg : ∀ y, 0 ≤ q y) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    {B : ℝ≥0∞}
    (hzero : ∀ y ∈ A ∩ frontier Y, q y = 0)
    (hbound : ∀ y ∈ frontier A ∩ closure Y, ENNReal.ofReal (q y) ≤ B)
    {x : ℂ} (hx : x ∈ Y)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ y ∈ closure Y, |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
      ∀ y ∈ Y, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    ENNReal.ofReal (q x) ≤ B * planarBrownianMotion x
      {ω | ContinuousPath.exitTime A ω ≤ hittingTime (A \ Y) ω} :=
  ofReal_le_boundary_mul_harmonicMeasure_of_exitExpectation hA hY hAb hYA hqmeas
    hqnonneg hM hzero hbound hx
    (le_integral_exitTime_of_generator_nonneg_approximation hY (hAb.subset hYA) hqmeas hM hx happrox)

end HarmonicBalls.Section6
