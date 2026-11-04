import HarmonicBalls.Draft.Section5
import HarmonicBalls.Proposed.LQG

/-!
# Local measurability of cluster containment

The proof of Proposition 1.3, corrected paper lines 1035–1040, uses the
local dependence of the obstacle problem on the measure. This step isolates
the measurable dependence of the containment event; Fact 2.1 II supplies
only the locality of the mass of each deterministic open set.
-/

namespace HarmonicBalls

open MeasureTheory Set

universe u

/-- Measurable dependence of the bounded-domain cluster containment event on
`h|_U`, from Fact 2.1 II and the obstacle construction. This is the remaining
measure-locality bridge in the proof at lines 1035–1040. -/
def ClusterContainmentLocalityStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    LQGMeasureLocality P γ α₀ hC hcirc →
  ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U → ∀ x ∈ U, ∀ t : ℝ, 0 < t →
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      {ω | closure (clusterOn (μ ω) U x t) ⊆ U} =ᵐ[P] E

end HarmonicBalls
