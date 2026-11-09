import HarmonicBalls.FirstPass.S11c.Assembly110
import HarmonicBalls.FirstPass.S11c.Ref11_7
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# First pass, Section 11, the shifted event (fp-S11c, owner n1)

Each theorem `firstPass_<sec>_<k>` concludes the Draft statement of a numbered result of Section 11
(`HarmonicBalls/Draft/Section11.lean`). Its hypotheses are Draft statements, EXTERNAL frozen Props of
`FirstPass/Frozen/S11c.lean` and `FirstPass/Frozen/*`, and the staged `Proposed/` inputs (operator ruling 19:45 UTC).

* Lemma 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, Draft/Section11.lean:214): `firstPass_11_10`, paper
  lemma:mass-diam (lines 3071-3112) and the proof of Lemma 11.10 (`prop:mass-diam-gen`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- FIRST-PASS, Lemma 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, Draft/Section11.lean:214). For closed dyadic
squares `S₁ ⊆ S₂` with `S₂` disjoint from the unit circle and `C > ε > 0`, the event that the internal diameter of `S₂`
is at most `ε` and the mass of `S₁` is at least `C` has a measurable subset of positive probability.

Hypotheses: the frozen Props `DyadicCellDiamSmallFrozen`, `CameronMartinEventTransferFrozen`,
`LQGMeasureSquarePositiveFrozen`, `LQGMeasureSquareMeasurableFrozen`, `LQGMetricSupMeasurableFrozen`,
`ConnectedSquareUnionDiamFiniteFrozen`, `WeylInternalClosedFrozen`, `LQGMetricContinuousShiftFactI`, and the measurability
of the Weyl-shifted metric and measure `WeylShiftedSupMeasurableFrozen`, `WeylShiftedMassMeasurableFrozen` (operator ruling
19:45 UTC, item n1 (1)); and the staged Proposed field axioms `LQGMetricFieldAxioms`, quantified over the field objects
(operator ruling 19:45 UTC, item n1 (2)). -/
theorem firstPass_11_10.{u}
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen) (hFactI : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  intro γ α₀ ξ hγ hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD S₁ S₂ hS₁ hS₂ hS12 hdisj C ε hε hεC
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  exact shifted_event_pos_11_10 hγ hγ2 hα P hGFF hμ hD (hAx γ ξ α₀ Ω P hC hcirc) hS₁ hS₂ hS12 hdisj
    hε hεC hDC hCM hPos hMassM hSupM hFin hW hFactI
    (fun f hf1 hf2 hf3 => hM1 γ α₀ ξ hγ hγ2 hα Ω P hC hcirc μ D hGFF hμ hD f hf1 hf2 hf3 S₂ hS₂)
    (fun f hf1 hf2 hf3 => hM2 γ α₀ ξ hγ hγ2 hα Ω P hC hcirc μ D hGFF hμ hD f hf1 hf2 hf3 S₁ hS₁)

#print axioms firstPass_11_10

/-- **Lemma 11.7 (first pass, `firstPass_11_7`)**: many cone-bad scales, with `δ = p / 8`, where `p` is the positive
probability lower bound supplied by Lemma 11.8 at `(γ, γ)` (not necessarily an exact event probability). Route (B2 sections 5-8): `ae_eventually_ncard_of_fixedRoot` with the fixed-root input
`hRef_of_decoder`. Frozen inputs: `ConeBadEventProbabilityStmt` (hypothesis Q2, Lemma 11.8 at `(γ, γ)`),
`LocalCampbellMarkedRestrictionFrozen`, `LQGMeasureOfProfileMeasurableFrozen`, `LocalLQGDecoderCommonFrozen`,
`CameronMartinLocallyLipschitzShiftAbsCont`. Proposed inputs, universal over the probability space:
`LQGMeasureCoordChange`, `LQGMeasureExistence`, `LQGMeasureNonatomic`. The translation `hW'` is proved
(`isWholePlaneGFF_translate`), not assumed. -/
theorem firstPass_11_7.{u}
    (hPos : ConeBadEventProbabilityStmt.{u}) (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u}) (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hCC : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α₀ hC hcirc)
    (hNA : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ManyConeBadScalesStmt.{u} := by
  intro γ α₀ hγ0 hγ2 hα Q hQ M hM
  obtain ⟨p, hp, hPos'⟩ := hPos γ γ hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) Q hQ M hM
  have hp0 : 0 < p := hp.1
  refine ⟨p / 8, ⟨div_pos hp0 (by norm_num), by linarith [hp.2]⟩, ?_⟩
  intro Ω _ P hC hcirc μ hh hμ
  have := hh.isProbabilityMeasure
  exact ae_eventually_ncard_of_fixedRoot hCamp hγ0 hγ2 hα hh hμ (hNA γ α₀ Ω P hC hcirc) hQ
    (hRef_of_decoder hDec hDecFrozen hCM hCC hE hγ0 hγ2 hα hQ hp0 hPos' hh hμ)

end HarmonicBalls.S11c
