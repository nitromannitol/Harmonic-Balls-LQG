import HarmonicBalls.Proofs.Sec8.TypicalPointStatement
import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic
import HarmonicBalls.Proofs.Sec2.Assembly

/-! # Lemma 8.2 from the staged LQG inputs and one rooted comparison

Lemma 8.2 (`TypicalPointManyGoodScalesStmt`, lemma:mu_h-doubling-and-harnack) follows from the staged whole-plane
LQG inputs and the single explicit rooted and centred measure-law comparison `hcomparison`, which is the proof
obligation of `typicalPointManyGoodScalesStmt_of_ambientLaw` (Proofs/Sec8/TypicalPointStatement.lean). The good-annulus
subrange step and the full-support statement are derived from volume growth here, so they are not hypotheses.

The imported Section 6 and Section 8 chains use Leonardo Bonanno's LatticeProb formalization of the Gwynne-Miller
lemma and of the pointwise ergodic theorem (`LatticeProb.Prob.Birkhoff`).
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Lemma 8.2 from the staged LQG inputs and the rooted comparison `hcomparison`. -/
theorem typicalPointManyGoodScalesStmt_of_literature
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
    TypicalPointManyGoodScalesStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  have hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hEx Ω P γ 0 hC hcirc
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC0 hW hE0 hN
  exact typicalPointManyGoodScalesStmt_of_ambientLaw hgrowth
    (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth)
    (Section6.goodAnnuliSubRangeStep_of_volumeGrowth hgrowth hAff hCC0)
    hEx hW hAff hCC hcomparison

end HarmonicBalls
