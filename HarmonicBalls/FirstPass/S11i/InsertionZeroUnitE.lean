import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDoubled
import HarmonicBalls.FirstPass.S11af
import HarmonicBalls.FirstPass.Frozen.S11i

/-!
# Insertion-zero unit frequency of a coding event (fp-S11i-insertion-zero-unit-E, n4)

`InsertionZeroUnitStmt.{0} γ E U V W T Q' Q δ M` (`S11i/Step8PhysExists.lean:85`) for a coding event `E` of the
Lemma 11.12 construction. The proof is the doubled-disc route of `S11i/HzoomUnitBallDoubled.lean`: for every
whole-plane model `(P, hC, hcirc, μ, D)` with insertion zero, the builder `step8UnitBallInputs2_of` produces the
inputs `Step8UnitBallInputs2` (root disc `ball c r`, decoder disc `ball c (2r)`), and `unitBallFrequencyModels_of_inputs2`
gives `UnitBallFrequencyStmt` at every `q` with `CommonProb γ E q`.

Inputs (all binders; none is proved here):
* frozen: `hK` (`LocalMeasureKernelStmt`, `S11r/Frozen.lean:144`), `hR` (`LocalMetricReplacementStmt` at `ξ = lqgXi γ`,
  `S11r/LocalMetricReplacement.lean:58`), `hfr` (`RootedPhysicalMetricContinuousAtInsertionFrozen`), `hPos`
  (`LQGMeasureSquarePositiveFrozen`);
* Proposed: `hNon` (`LQGMeasureNonatomic`, `Proposed/LQG.lean:77`; operator-confirmed 2026-11-10), in its universal form;
* frozen, Sub form: `hA10` (`DMSLemmaA10WholePlaneMarkedSub`, `Frozen/S11i.lean:58`), converted to the marked form by
  `HarmonicBalls.dmsA10Marked_of_sub` at the fixed `0 < γ < 2`;
* NAMED: `hHref`, the `href` field of `Step8UnitBallInputs2` (reference observations avoid the failure set at `q`),
  in its universal form over whole-plane models and over every `q` with `CommonProb γ E q`. It is the one remaining
  named input of this file; its instance for the ball decoders is the work of n2 (`S11r/RootedHrefBall.lean`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iInsertionZeroUnitE

open HarmonicBalls FirstPassS11ai
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

/-- **Insertion-zero unit frequency of a coding event `E`, from the doubled-disc inputs.** For a coding event `E` of
the Lemma 11.12 construction, given the frozen and Proposed inputs above and the named `href` input `hHref` (universal
over whole-plane models and over the common probabilities `q` of `E`), `E` has the insertion-zero unit frequency
`InsertionZeroUnitStmt.{0}`: for every whole-plane insertion-zero model and every `q` with `CommonProb γ E q`, the
unit-ball frequency of the certificate events is `q` (Lemma 11.13, Step 8, unit scale). -/
theorem insertionZeroUnit_of_href {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hNon : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.LQGMeasureNonatomic P γ 0 hC hcirc)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), HarmonicBalls.DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hHref : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
        (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' → HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q) :
    InsertionZeroUnitStmt.{0} γ E U V W T Q' Q δ M := by
  intro Ω _ P hC hcirc μ D hG hμ hD q hq
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  have inp : Step8UnitBallInputs2 P γ (lqgXi γ) q δ M U V W T Q' Q :=
    step8UnitBallInputs2_of (P := P) (q := q) hγ0 hγ2 hK hR hfr hPos hgeo (hNon Ω P)
      (fun hC' hcirc' μ' => HarmonicBalls.dmsA10Marked_of_sub P γ hC' hcirc' μ' (hA10 Ω P hC' hcirc' μ') hγ0 hγ2)
      (hHref Ω P q hq)
  have hmod := unitBallFrequencyModels_of_inputs2 hγ0 hγ2 inp
  exact hmod hC hcirc μ D hG hμ hD

end HarmonicBalls.FirstPassS11iInsertionZeroUnitE

#print axioms HarmonicBalls.FirstPassS11iInsertionZeroUnitE.insertionZeroUnit_of_href
