import HarmonicBalls.Proofs.Sec8.OriginExplicitInputAssembly
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences

/-! # Conditional Section 8 exports

The imported Section 8 proof uses Leonardo Bonanno's `LatticeProb.Prob.Birkhoff`
formalization of the ergodic theorem. These examples expand each top-level
premise and conclusion, and check the applications without adding hypotheses.
-/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
universe u

example
    (hholder :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
    ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O))
    (hgrowth :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
    βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧ μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → (0 : ℝ) < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ (0 : ℝ) hcirc μ → ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
  IsWholePlaneGFF P hC hcirc → ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b))
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsLQGLimit γ (fun ε z => fieldCircleAverage α₀ (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
        ((μ ω).map fun x => (x - b) / a))
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → (0 : ℝ) < lqgQ γ →
    ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ (0 : ℝ) hcirc μ)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → (0 : ℝ) < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ (0 : ℝ) hcirc μ → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage (0 : ℝ) (hcirc ω)) f)
        ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) βminus 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N :=
  originManyGoodScalesStmt_of_explicit_inputs hholder hgrowth hatom hAff hCC hex hW

example
    (h32 :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
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
    (h611 :
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ C₃ : ℝ, 0 < C₃ → ∃ b ∈ Ioo (0 : ℝ) 1,
  ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₁p → 0 < C₂m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ ∈ ball (0 : ℂ) 1,
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal (α a N₀ C₁m) * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅)
    (h82 :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball (0 : ℂ) 1), ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N)
    :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    μ ω (frontier (cluster (μ ω) 1 z t)) = 0 :=
  boundaryMeasureZeroOfCompactClusterStmt_of_steps h32 h611 h82

/-- I2 supplies both numbered inputs, while 8.2 is still an explicit premise. -/
example (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} :=
  boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82

#print axioms originManyGoodScalesStmt_of_explicit_inputs
#print axioms boundaryMeasureZeroOfCompactClusterStmt_of_steps

end HarmonicBalls
