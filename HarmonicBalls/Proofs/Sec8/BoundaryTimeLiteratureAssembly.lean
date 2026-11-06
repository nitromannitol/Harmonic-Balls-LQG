import HarmonicBalls.Proofs.Sec7.LiteratureAssembly
import HarmonicBalls.Proofs.Sec8.TypicalPointLiteratureAssembly

/-! # Propositions 8.1 and 7.2 from the staged inputs and one rooted comparison

Proposition 8.1 (`BoundaryMeasureZeroOfCompactClusterStmt`) and Proposition 7.2 (`ClusterTimeContinuityStmt`) follow from
`clusterBoundary_and_timeContinuity_of_literature` (Proofs/Sec7/LiteratureAssembly.lean) with Lemma 8.2 supplied by
`typicalPointManyGoodScalesStmt_of_literature` (Proofs/Sec8/TypicalPointLiteratureAssembly.lean). The hypotheses are the
Green-potential clause of Proposition 2.5 (`hholder`), the staged LQG inputs and the rooted comparison `hcomparison`.

The imported Section 6, 7 and 8 chains use Leonardo Bonanno's LatticeProb formalization of the Gwynne-Miller lemma and
of the pointwise ergodic theorem (`LatticeProb.Prob.Birkhoff`).
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Propositions 8.1 and 7.2 from the Green-potential clause, the staged LQG inputs and `hcomparison`. -/
theorem boundary_and_timeContinuity_of_literature
    (hholder : GreenPotentialHolderStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α hC hcirc)
    (hcomparison : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
      (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ ν : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
      (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ),
      0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ γ hcirc ν →
      ∃ S : Measure Ω, P ≪ S ∧ AEMeasurable μ S ∧
        (∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω)) ∧
      ∃ (w : ℂ → ℝ≥0∞) (hw : Measurable w),
        (∀ z, w z ≠ 0) ∧ (∀ z, w z ≠ ∞) ∧
      ∃ ρ : ℕ → Measure ℂ, (∀ n, ρ n ≪ volume) ∧
      ∃ shift : ℕ → ℂ × Ω → Ω, (∀ n, Measurable (shift n)) ∧
      ∃ R : ℕ → ℂ → Measure Ω,
        (∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ
          (hGFF.aemeasurable_lqgMeasure hμ) (weightedLocalization w n)
          (measurableSet_weightedLocalization hw n) w hw) ≪
            shiftedRootReferenceLaw (ρ n) P (shift n)) ∧
        (∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z) ∧
        (∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S) ∧
        (∀ n, ∀ᵐ z ∂ρ n,
          (R n z).map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P.map ν)) :
    BoundaryMeasureZeroOfCompactClusterStmt.{u} ∧ ClusterTimeContinuityStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hEx Ω P γ 0 hC hcirc
  exact clusterBoundary_and_timeContinuity_of_literature hholder hDG hAff hCC0 hW hE0 hN
    (typicalPointManyGoodScalesStmt_of_literature hDG hAff hCC hW hEx hN hcomparison)

#print axioms boundary_and_timeContinuity_of_literature

end HarmonicBalls
