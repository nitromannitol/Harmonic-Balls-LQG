import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling

/-! # Cluster scale invariance -/

namespace HarmonicBalls

universe u

open MeasureTheory Set ProbabilityTheory
open scoped Pointwise

/-- The scale-invariance law for a fixed field, conditional on the staged
whole-plane GFF affine-invariance and LQG coordinate-change inputs and on
measurability of the cluster family. -/
theorem clusterScaleInvariance_of_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeas : ClusterFamilyMeasurabilityStep.{u})
    {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    IdentDistrib (fun ω (t : Ioi (0 : ℝ)) => cluster (μ ω) 1 z t)
      (fun ω (t : Ioi (0 : ℝ)) => k⁻¹ • cluster (μ ω) k (k • z)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)) P P :=
  clusterScaleInvariance_of_pathwise_and_measurable h hAff hCC hγ hγ2 hα hμ
    clusterPathwiseScaleStep_proved hmeas hk hz

end HarmonicBalls
