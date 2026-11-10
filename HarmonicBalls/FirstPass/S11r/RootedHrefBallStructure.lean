import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDoubled
import HarmonicBalls.FirstPass.S11r.RootedHrefBall

/-!
# The `Step8UnitBallInputs2` instance with the ball-metric `href` (fp-S11r-n4-instance-gaps, n2)

`step8UnitBallInputs2_ballMetric` is `HzoomUnitBallDoubled.step8UnitBallInputs2_of` with its `href` field supplied by
`HarmonicBalls.FirstPassS11rRootedHrefBall.href_ballMetric_of_inputs` (RootedHrefBall.lean), for every whole-plane model.

The only changes with respect to the one-model theorem are the universal forms of the per-model inputs:
* `hGa`, `hG0a` (the canonical field lies in `G`, `G0` almost surely) and `hCC`, `hνex` (coordinate change and existence on
  the translates) are taken for every whole-plane model `(hC', hcirc')`;
* `hq` (the frequency `q` is the canonical frequency of every model; `canonical_frequency_eq_of_models` gives this from one
  model when `q` is a step-8 frequency).
The containments `hCont`, `hU` are binders (the frozen containments of the pinch geometry, not derived here).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit HarmonicBalls.FirstPassS11iHzoom FirstPassS11ai
open HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11rRootedHrefBall
open HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassS11rRootedHrefBallStructure

/-- **The `Step8UnitBallInputs2` instance of the ball decoders, with the ball-metric `href` for every model.** -/
noncomputable def step8UnitBallInputs2_ballMetric {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hNat : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC' hcirc')
    (hA10 : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
      DMSLemmaA10WholePlaneMarked P γ hC' hcirc' μ')
    (hProf : HarmonicBalls.LQGMeasureOfProfileMeasurableFrozen.{0}) (hLenFr : HarmonicBalls.LQGMetricLengthUnivFrozen.{0})
    (hFieldFr : HarmonicBalls.LQGMetricFieldAxiomsUnivFrozen.{0})
    (hUax : HarmonicBalls.LQGMetricSatisfiesAxiomsUnivFrozen.{0}) (hXi : HarmonicBalls.LQGMetricExponentPositive)
    (hComp : HarmonicBalls.WeylMetricCompositionContinuousOuterFrozen)
    (hCont : FirstPassS11i.CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7))) (hF : MeasurableSet F)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0 ↔
        ballRestrictPairing 7 L ∈ F)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ γ Dμ Dd)
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G)
    (hGa : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ᵐ ω ∂P, alphaCanon γ hC' ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0)
    (hG0a : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ᵐ ω ∂P, alphaCanon γ hC' ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hCC : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ z : ℂ,
      LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC' hcirc' z) (S11c.translatedCircle hcirc' z))
    (hνex : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' → ∀ z : ℂ,
      LQGMeasureExistence P γ γ (S11c.translatedPairing hC' hcirc' z) (S11c.translatedCircle hcirc' z))
    (hq : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      q = (P {ω | alphaCanon γ hC' ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) :
    Step8UnitBallInputs2 P γ ξ q δ M U V W T Q' Q :=
  step8UnitBallInputs2_of hγ0 hγ2 hK hR hfr hPos hgeo hNat hA10
    (fun hC' hcirc' μ' _𝔇 h𝔇 hG' hμ' p hp =>
      href_ballMetric_of_inputs hCM hB hγ0 hγ2 hK hR hfr hG' μ' hμ' h𝔇 p hp hF (pinchOmegaGeom W Q δ) U V W T Q' Q
        hCont hU Dμ Dd hFdef hDμ hDd (hIdγ) hPos G hGm (hGa hC' hcirc' hG') hGreg G0 hG0 (hG0a hC' hcirc' hG') hinv hstep
        (hA10 hC' hcirc') hProf hLenFr hFieldFr hfr hUax hXi hComp (hCC hC' hcirc' hG') (hνex hC' hcirc' hG')
        (hq hC' hcirc' hG'))

end HarmonicBalls.FirstPassS11rRootedHrefBallStructure

#print axioms HarmonicBalls.FirstPassS11rRootedHrefBallStructure.step8UnitBallInputs2_ballMetric
