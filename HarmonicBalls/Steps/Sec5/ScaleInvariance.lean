import HarmonicBalls.Draft.Section5

/-!
# Lemma 5.7: scale invariance of clusters

The proof uses the normalized pullback measure, its law, the pathwise
change of scale of the obstacle problem, and measurability of the resulting
cluster-valued map. These steps retain the simultaneous pathwise equality
in all centers and times used in the proof of Theorem 5.5.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped Pointwise

universe u

/-- The measure of the normalized field `h(k ·) - h_k(0)`, expressed using
coordinate change and Weyl scaling. -/
noncomputable def normalizedPullbackMeasure (γ α₀ k : ℝ) (hcirc : ℝ → ℂ → ℝ)
    (μ : Measure ℂ) : Measure ℂ :=
  ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k +
    fieldCircleAverage α₀ hcirc k 0)))⁻¹ • Measure.map (fun x : ℂ => k⁻¹ • x) μ

/-- The normalized pullback measure has the law of the original LQG measure. -/
def NormalizedPullbackMeasureLawStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ k : ℝ, 0 < k → IdentDistrib μ
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) P P

/-- Scaling the obstacle problem gives the cluster identity simultaneously
for all centers in the unit ball and positive times. -/
def ClusterPathwiseScaleStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ k : ℝ, 0 < k → ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster (normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) 1 z t =
        k⁻¹ • cluster (μ ω) k (k • z)
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)

/-- Measurability of the positive-time cluster family as a function of the
LQG measure, with respect to its law. -/
def ClusterFamilyMeasurabilityStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ z ∈ ball (0 : ℂ) 1, AEMeasurable
      (fun ν : Measure ℂ => fun t : Ioi (0 : ℝ) => cluster ν 1 z t) (Measure.map μ P)

/-- Lemma 5.7 from the normalized measure law, pathwise scale change and
cluster-family measurability. -/
theorem clusterScaleInvariance_of_steps (hlaw : NormalizedPullbackMeasureLawStep.{u})
    (hscale : ClusterPathwiseScaleStep.{u}) (hmeas : ClusterFamilyMeasurabilityStep.{u}) :
    ClusterScaleInvarianceStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ k hk z hz
  have h := (hlaw γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk).comp_of_aemeasurable
    (hmeas γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ z hz)
  apply h.trans
  apply IdentDistrib.of_ae_eq h.aemeasurable_snd
  filter_upwards [hscale γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk] with ω hω
  funext t
  exact hω z hz t t.property

end HarmonicBalls
