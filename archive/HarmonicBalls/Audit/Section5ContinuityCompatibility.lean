import HarmonicBalls.Steps.Sec5.ContinuityAssembly
import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Conditional continuity and compatibility checks

Expanded composition checks. The imported dependency tree uses Leonardo
Bonanno's `LatticeProb.Prob.Birkhoff` formalization. -/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter Topology
open scoped Pointwise
universe u

example
    (h71 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ r ∈ Ioo (0 : ℝ) 1,
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)}))
    (h33 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t₁ t₂ r : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    cluster (μ ω) r z t₁ ⊆ cluster (μ ω) r z t₂)
    (h72 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
  ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      closure (cluster (μ ω) 1 z (t + ε)) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) (C * ε ^ (1 / (4 * βminus))))
    (hboundary : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t →
      ¬ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧
        ∀ t' ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε)
    : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2),
    ⋂ t ∈ Ioi (0 : ℝ), closure (cluster (μ ω) 1 z t) = {z} ∧
    ∀ t : ℝ, 0 < t → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧ ∀ t' ∈ Icc t (t + δ),
      closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε :=
  clusterContinuity_of_boundaryTouching h71 h33 h72 hboundary

example
    (h32 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    IsOpen (cluster (μ ω) r z t) ∧ IsConnected (cluster (μ ω) r z t) ∧
    ∃ ν : Measure ℂ, IsLocallyFiniteMeasure ν ∧
      ν.restrict (ball 0 r) ≪ (μ ω).restrict (ball 0 r) ∧
      ν.restrict (ball 0 r) ≤ (μ ω).restrict (ball 0 r) ∧
      HasLaplacian (leastSupersolution (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t))) 0
        (ball 0 r) ∧
      HasLaplacian (odometer (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 r))
    (hcompat : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → U ⊆ ball (0 : ℂ) r → ∀ z ∈ U, ∀ t : ℝ, 0 < t →
      (closure (cluster (μ ω) r z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U) →
      cluster (μ ω) r z t = clusterOn (μ ω) U z t)
    : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, (SatisfiesHarmonicBallConditions (μ ω) (Λhat ω z) z ∧ (∀ t : ℝ, 0 < t → IsSubharmonicBall (μ ω) (Λhat ω z t) z) ∧ ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λhat ω z t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r → Λhat ω z t = interior (closure (cluster (μ ω) r z t)))) →
  ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ U,
    (closure (Λhat ω z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U) →
      closure (Λhat ω z t) = closure (clusterOn (μ ω) U z t) :=
  clusterStrongCompatibility_of_steps h32 hcompat

end HarmonicBalls
