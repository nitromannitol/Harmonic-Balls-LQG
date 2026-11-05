import HarmonicBalls.Proofs.Sec10.PrevalenceCrossingAssembly

/-! # Conditional verification of the Section 10 crossing exports

The examples expose the conditional premises and check the frozen conclusion;
they neither establish the premises nor approve their sources. The imported
annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`; the field-law bridge uses
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

universe u

-- I2 and zero-strength existence, both expanded to their defining propositions.
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
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → 0 < lqgQ γ →
      ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ) :
    ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_zero_existence hI2 hE0

-- All three staged propositions are expanded, including the probability tail.
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
    ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_three_staged_inputs hDG hCC hE

-- Check the conclusion independently at the printed quantifier order and carrier.
example (h : ClusterBoundedCrossingsStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1, ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
    ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ z : ℂ,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ({C ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) |
        (closure C ∩ sphere w (ρ / 3)).Nonempty ∧
        (closure C ∩ sphere w (2 * ρ)).Nonempty}).encard ≤ ⌈1 / α⌉₊ := h

#print axioms clusterBoundedCrossings_of_volumeGrowth_and_zero_existence
#print axioms clusterBoundedCrossings_of_three_staged_inputs

end HarmonicBalls
