import HarmonicBalls.FirstPass.S11i.Step8Event
import HarmonicBalls.FirstPass.S11m.Final11_12

/-!
# Lemma 11.12 event at gamma from the named inputs of firstPass_11_12_final (fp-S11i-11-13d, n3)

Replaces the hypothesis CorrectedLemma11_12Stmt of pinchEventGamma_exists (Step8Event.lean) by the named inputs of
firstPass_11_12_final (S11m/Final11_12.lean:131), with the same binders in the same order. No new input.
-/

namespace HarmonicBalls.FirstPassS11iPinch12

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- The 11.12 event at the insertion gamma (B4), from the inputs of firstPass_11_12_final. -/
theorem pinchEventGamma_of_11_12_inputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    {U V W T Q' Q : Set ℂ} {δ₀ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ₀)
    {γ ξ M : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaStmt.{u} U T Q' Q γ ξ M E :=
  HarmonicBalls.pinchEventGamma_exists (HarmonicBalls.S11m.Final11_12.firstPass_11_12_final hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE hfr hmass hCMAbs hCMRew hComp hDsm hMf hDiam hMk hholder) hgeo hγ hγ2 hM

end HarmonicBalls.FirstPassS11iPinch12
