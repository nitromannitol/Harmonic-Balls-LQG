import HarmonicBalls.Proofs.Sec11.AnnulusMassStagedClosure
import HarmonicBalls.Proofs.Sec11.NotLipschitz
import HarmonicBalls.Proofs.Sec11.NotMetricBallGrowth
import HarmonicBalls.Proofs.Sec2.Assembly

/-!
# Section 11 results from the staged inputs and their named open inputs

This file restates the reductions of Proposition 11.2 (`HarmonicBallNotLipschitzStmt`, through Lemma 11.5 and the cone
input Lemma 11.7) and Proposition 11.11 (`HarmonicBallNotMetricBallStmt`, through the pinch input Lemma 11.13) with
Lemma 11.6 discharged by `annulusMassBoundByHarmonicChainStmt_of_stagedInputs`. The LQG volume growth I2 comes from
the Section 2 literature wrapper.

Explicit hypotheses in addition to the staged LQG inputs of `HarmonicBalls.Proposed.LQG` and the two section statements
`h8` and `h61` of `AnnulusMassStagedClosure`:
* `ManyConeBadScalesStmt` (Lemma 11.7) for Proposition 11.2 and `NoConeConditionStmt` (Lemma 11.5);
* `ManyPinchScalesStmt` (Lemma 11.13) for Proposition 11.11;
* the staged metric-field axioms `LQGMetricFieldAxioms` (Proposed/LQG.lean) for Proposition 11.11.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Lemma 11.5 (`NoConeConditionStmt`) from Lemma 11.7 and the staged inputs. -/
theorem noConeConditionStmt_of_stagedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u}) :
    NoConeConditionStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  exact noConeConditionStmt_of_comparison_and_coneScales
    (annulusMassBoundByHarmonicChainStmt_of_stagedInputs hDG hAff hCC hW hE hN h8 h61) hmany
    (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC0 hW hE hN)

/-- Proposition 11.2 (`HarmonicBallNotLipschitzStmt`) from Lemma 11.7 and the staged inputs. -/
theorem harmonicBallNotLipschitzStmt_of_stagedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (hmany : ManyConeBadScalesStmt.{u}) :
    HarmonicBallNotLipschitzStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  exact harmonicBallNotLipschitzStmt_of_comparison_and_coneScales
    (annulusMassBoundByHarmonicChainStmt_of_stagedInputs hDG hAff hCC hW hE hN h8 h61) hmany
    (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC0 hW hE hN)

/-- Proposition 11.11 (`HarmonicBallNotMetricBallStmt`) from Lemma 11.13, the staged inputs and the staged
metric-field axioms `LQGMetricFieldAxioms`. -/
theorem harmonicBallNotMetricBallStmt_of_stagedInputs
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (hmany : ManyPinchScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} := by
  have hCC0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc
  exact harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth
    (annulusMassBoundByHarmonicChainStmt_of_stagedInputs hDG hAff hCC hW hE hN h8 h61) hmany
    (lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff hCC0 hW hE hN) hmetricAxioms

end HarmonicBalls

#print axioms HarmonicBalls.noConeConditionStmt_of_stagedInputs
#print axioms HarmonicBalls.harmonicBallNotLipschitzStmt_of_stagedInputs
#print axioms HarmonicBalls.harmonicBallNotMetricBallStmt_of_stagedInputs
