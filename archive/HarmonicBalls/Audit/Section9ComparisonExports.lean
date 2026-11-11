import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Conditional verification of the Section 9 comparison exports

The assumptions are exposed, not proved or source-approved. The imported Section 6
annulus iteration uses Leonardo Bonanno's work in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`; field-law bridges use
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter Topology
universe u

-- Three staged inputs, including the polynomial-probability quantifiers.
example
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 →
      ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ βlower βupper : ℝ, 0 < βlower → βlower < 2 / (2 + γ) ^ 2 →
      2 / (2 - γ) ^ 2 < βupper →
      ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ > 0, ∀ ε : ℝ, 0 < ε → ε < r₀ →
        P {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ βlower))) ∧
          ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
            μ ω (ball z (ε ^ βupper)) ≤ ENNReal.ofReal ε}ᶜ ≤
              ENNReal.ofReal (C * ε ^ p))
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
        IsLQGLimit γ (fun ε z => fieldCircleAverage 0 (hcirc ω) (‖a‖ * ε)
          (a * z + b) + lqgQ γ * Real.log ‖a‖)
          ((μ ω).map fun x => (x - b) / a))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ α hcirc μ) :
    HarmonicBallBoundarySubsetStmt.{u} ∧ RegularOpenEqOfAEEqStmt.{u} :=
  section9_comparison_lemmas_of_existence hDG hCC hE

-- I2 and 8.2 remain explicit and are expanded at their defining types.
example
    (hI2 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
        IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
        βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
        max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
          ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧
            μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    (h82 : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball (0 : ℂ) 1), ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales hI2 h82

-- Check the actual frozen targets against their full outer quantifier order.
example (h : HarmonicBallBoundarySubsetStmt.{u}) :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (R t : ℝ), z ∈ ball (0 : ℂ) R → closure A ⊆ ball (0 : ℂ) R →
    IsHarmonicBallGen (μ ω) A z → 0 < t → μ ω A = ENNReal.ofReal t →
    frontier A ⊆ closure (Λhat ω z t) := h

example (h : RegularOpenEqOfAEEqStmt.{u}) :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ X Y : Set ℂ, IsOpen X → IsOpen Y → IsRegularOpen X → IsRegularOpen Y →
    μ ω (X \ Y) = 0 → μ ω (Y \ X) = 0 → X = Y := h

example (h : SubharmonicBallUniquenessWeakStmt.{u}) :
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R → z ∈ ball (0 : ℂ) R →
    closure A ⊆ ball (0 : ℂ) R → IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
    cluster (μ ω) R z t ⊆ A ∧ μ ω (A \ regularizedCluster (μ ω) R z t) = 0 := h

end HarmonicBalls
