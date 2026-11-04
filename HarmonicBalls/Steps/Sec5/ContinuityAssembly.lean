import HarmonicBalls.Steps.Sec5.ClusterContinuity
import HarmonicBalls.Steps.Sec5.CompactContinuity

/-!
# Proposition 5.2 and the boundary-touching case

Proposition 7.2 proves right continuity up to exit. This reduction exposes
the missing boundary-touching case (GRAPH G12) as a separate step.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- Right continuity at times when the cluster is not compactly contained in `B₁`. -/
def ClusterBoundaryTouchingRightContinuityStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t →
      ¬ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧
        ∀ t' ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε

/-- The full right-continuity assertion from compact continuity and the
boundary-touching case. -/
theorem clusterRightContinuity_of_steps (hcompact : ClusterCompactRightContinuityStmt.{u})
    (hboundary : ClusterBoundaryTouchingRightContinuityStep.{u}) : ClusterRightContinuityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcompact γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hboundary γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hc hb
  intro z hz t ht
  by_cases h : closure (cluster (μ ω) 1 z t) ⊆ ball 0 1
  · exact ⟨1, by norm_num, fun ε hε => hc z hz t ht h ε hε.1⟩
  · exact hb z hz t ht h

/-- Proposition 5.2 from Propositions 7.1 and 7.2, Lemma 3.3, and the
boundary-touching case. -/
theorem clusterContinuity_of_boundaryTouching (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h33 : ClusterMonotoneStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hboundary : ClusterBoundaryTouchingRightContinuityStep.{u}) : ClusterContinuityStmt.{u} :=
  clusterContinuity_of_steps h71
    (clusterRightContinuity_of_steps (clusterCompactRightContinuity_of_steps h33 h72) hboundary)

end HarmonicBalls
