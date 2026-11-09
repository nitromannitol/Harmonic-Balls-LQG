import HarmonicBalls.FirstPass.S11.MetricBall
import HarmonicBalls.FirstPass.S11.Geometry
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Proofs.Sec11.NotLipschitz
import HarmonicBalls.Proofs.Sec11.ConeStatement
import HarmonicBalls.Proofs.Sec11.ComparisonConsequences
import HarmonicBalls.Proofs.Sec11.NotMetricBallGrowth
import HarmonicBalls.Steps.Sec11.ConeProbabilityFromLiterature

/-!
# First pass, Section 11 (fp-S11, owner n3)

Each theorem `firstPass_11_<k>` concludes the Draft statement of a numbered result of Section 11
(`HarmonicBalls/Draft/Section11.lean`). Its hypotheses are only Draft statements of other numbered results and
EXTERNAL Props (FIRST-PASS FROZEN Props in `FirstPass/Frozen/S11.lean`, the staged `Proposed/` inputs, the
cited Draft statements).

Status (round 1):
* Lemma 11.14 (`PinchEventMetricBallConsequenceStmt`): `firstPass_11_14`, from the staged input
  `LQGMetricFieldAxioms` (Proposed/LQG.lean; Fact 2.2 I-IV for the field, pending operator source-check).
* Definitions 11.1, 11.3, 11.4 are in `Defs/Geometry.lean` (no theorem; Draft "-").
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

open FirstPassS11

/-- FIRST-PASS, Lemma 11.14 (lemma:geometric-event-consequence, paper line 3264), for the Draft statement
`PinchEventMetricBallConsequenceStmt` (`Draft/Section11.lean:275`). The only input beyond the Draft is the staged
field axioms `LQGMetricFieldAxioms` (Proposed/LQG.lean), used for the length-metric property of `D_h` (Fact 2.2 I)
and the Weyl-scaling identity of the metric. -/
theorem firstPass_11_14.{u} (hAx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    PinchEventMetricBallConsequenceStmt.{u} := by
  intro U T Q' Q hc γ α₀ ξ hγ hγ₂ hα Ω _ P hC hcirc μ D hg hm hd
  obtain ⟨𝔇, h𝔇, hae⟩ := hd
  have hax := hAx Ω P γ ξ α₀ hC hcirc hg hγ hγ₂ hα 𝔇 h𝔇
  filter_upwards [hax.1, hae] with ω hωI hωD
  have hDlen : IsEuclideanLengthMetric (D ω) := by
    have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      obtain ⟨h0, heq⟩ := hωD u v
      rw [← heq, ENNReal.toReal_ofReal h0]
    rw [hfun]
    exact hωI.2
  intro M _ z r hr h0 u hu hev hfr
  obtain ⟨hev1, hev2, -⟩ := hev
  exact metricBall_of_pinch_event hDlen hc hr h0 hu hev1 hev2 hfr

#print axioms firstPass_11_14

/-- FIRST-PASS, Proposition 11.2 (prop:not-balls, paper line 2816), for `HarmonicBallNotLipschitzStmt`
(`Draft/Section11.lean:136`). The printed proof (lines 2991-3012) uses Lemma 11.5 only; the transfer from typical
boundary points to Lebesgue-a.e. time is `ae_time_property_of_ae_frontier` (Steps/Sec11/TimeFrontierProperty.lean),
which needs no measurability of the property (compact exhaustion of the good boundary points). -/
theorem firstPass_11_2.{u} (h5 : NoConeConditionStmt.{u}) : HarmonicBallNotLipschitzStmt.{u} :=
  harmonicBallNotLipschitzStmt_of_noConeCondition h5

/-- FIRST-PASS, Lemma 11.5 (lemma:no-exterior-cone-condition, paper line 2846), for `NoConeConditionStmt`
(`Draft/Section11.lean:145`). Uses the Draft statements of Lemma 11.6 (`AnnulusMassBoundByHarmonicChainStmt`), Lemma 11.7
(`ManyConeBadScalesStmt`) and the LQG volume growth I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean:122). The
positivity of the annular Green potential in the printed proof (lines 2952-2990) is supplied by full support
(`LQGMeasureFullSupportStmt`, a consequence of I2 in Draft/Section2.lean:109), since annuli are non-empty open sets. -/
theorem firstPass_11_5.{u} (h6 : AnnulusMassBoundByHarmonicChainStmt.{u})
    (h7 : ManyConeBadScalesStmt.{u}) (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    NoConeConditionStmt.{u} :=
  noConeConditionStmt_of_comparison_and_coneScales h6 h7 hI2

/-- FIRST-PASS, Lemma 11.6 (lemma:harmonic-comparison-chain, paper line 2856), for
`AnnulusMassBoundByHarmonicChainStmt` (`Draft/Section11.lean:160`). The printed proof applies Lemmas 6.8 and 6.10 to
clusters in balls `B_R` (printed as "extend verbatim"); the reduction used here is
`annulusMassBoundByHarmonicChainStmt_of_volumeGrowth` (`Proofs/Sec11/ComparisonConsequences.lean:18`), which goes
through `annulusMassBoundByHarmonicChainStmt_of_scaledField` (`Proofs/Sec11/AnnulusMassComparison.lean:81`: boundary
nullity from Proposition 8.1 and pathwise cluster scaling). The hypotheses are Draft statements (I2, Lemmas 6.8, 6.10,
the boundary statement of Section 8, Theorem 5.5) and the staged affine-invariance and coordinate-change props. -/
theorem firstPass_11_6.{u} (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u}) (h610 : OdometerBoundByAnnulusMassStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u}) (hexist : ExistenceHarmonicBallsStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    AnnulusMassBoundByHarmonicChainStmt.{u} :=
  annulusMassBoundByHarmonicChainStmt_of_volumeGrowth hI2 h68 h610 h8 hexist hAff hCC

/-- FIRST-PASS, Lemma 11.8 (lemma:positive-probability, paper line 2903), for `ConeBadEventProbabilityStmt`
(`Draft/Section11.lean:186`), from the staged whole-plane ball-mass estimate `WholePlaneLQGBallMassBounds`, the
coordinate change `LQGMeasureCoordChange` and the existence `LQGMeasureExistence` (all `Proposed/LQG.lean`, pending
operator source-check). -/
theorem firstPass_11_8.{u}
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    ConeBadEventProbabilityStmt.{u} :=
  coneBadEventProbability_of_literature hDG hCC hE

/-- FIRST-PASS, Proposition 11.11 (prop:not-metric-balls, paper line 3150), for `HarmonicBallNotMetricBallStmt`
(`Draft/Section11.lean:231`). Uses the Draft statements of Lemma 11.6, Lemma 11.13 (`ManyPinchScalesStmt`) and the
volume growth I2; the metric-field axioms are the staged `LQGMetricFieldAxioms`. -/
theorem firstPass_11_11.{u} (h6 : AnnulusMassBoundByHarmonicChainStmt.{u})
    (h13 : ManyPinchScalesStmt.{u}) (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallStmt.{u} :=
  harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth h6 h13 hI2 hmetricAxioms

#print axioms firstPass_11_2
#print axioms firstPass_11_5
#print axioms firstPass_11_6
#print axioms firstPass_11_8
#print axioms firstPass_11_11

end HarmonicBalls
