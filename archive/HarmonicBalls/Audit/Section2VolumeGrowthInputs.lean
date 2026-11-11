import HarmonicBalls.Proofs.Sec8.OriginLiteratureAssembly

/-! # Audit of the Section 2 literature-to-I2 composition

The imported Section 8 proof uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
These examples check conditional applications, not the source validity of inputs.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/- The producer has exactly these six expanded top-level logical inputs. -/
example
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ βlower βupper : ℝ, 0 < βlower → βlower < 2 / (2 + γ) ^ 2 →
      2 / (2 - γ) ^ 2 < βupper → ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ > 0,
      ∀ ε : ℝ, 0 < ε → ε < r₀ → P ({ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        ENNReal.ofReal ε ≤ μ ω (ball z (ε ^ βlower))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
        μ ω (ball z (ε ^ βupper)) ≤ ENNReal.ofReal ε})ᶜ ≤ ENNReal.ofReal (C * ε ^ p))
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsWholePlaneGFF P
        (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b))
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ → ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
        IsLQGLimit γ (fun ε z => fieldCircleAverage 0 (hcirc ω) (‖a‖ * ε) (a * z + b) +
          lqgQ γ * Real.log ‖a‖) ((μ ω).map fun x => (x - b) / a))
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ → ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
        IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
          ((μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
      βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧
          μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus) := by
  exact lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC hW hE hN

#print axioms lqgVolumeGrowthAllScalesStmt_of_literature
#print axioms rescaledBallMassUniformStep_of_DG
#print axioms lqgVolumeGrowthAllScalesStmt_of_ballMass
#print axioms originManyGoodScalesStmt_of_literature

end HarmonicBalls
