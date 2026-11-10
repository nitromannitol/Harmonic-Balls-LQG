import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDoubled
import HarmonicBalls.FirstPass.S11af
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.FirstPass.S11i.HFdefOnG
import HarmonicBalls.FirstPass.S11i.CertificateCanonical

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
open HarmonicBalls.S11ax HarmonicBalls.S11m HarmonicBalls.S11m.CertificateAssembly HarmonicBalls.S11c

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


/-- **Insertion-zero unit frequency of the Lemma 11.12 coding set, with `hFdef` on `G`.** For
`E := decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M`, the href field of
`insertionZeroUnit_of_href` is `ae_href_of_covariance_G` (`S11i/HFdefOnG.lean`) with `hFdef` on `G` from
`hFdef_decoded_on_G`. The named inputs are the G-properties `hmet`, `hdec`, `hfin`, `hEmeas`, and the two rooted inputs
`hCovU` (n2's covariance for the ball decoders) and `hGrootU` (rooted membership in `G`). -/
theorem insertionZeroUnit_decoded_on_G {γ δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hNon : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.LQGMeasureNonatomic P γ 0 hC hcirc)
    (hA10 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), HarmonicBalls.DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (I : HarmonicBalls.S11am.PinchCountSets V W T Q' Q δ)
    (Ψc : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ → ℂ → ℝ)
    (Φμ : ModConstTestPairings (ball (0 : ℂ) 7) → Measure ℂ)
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (Ψc (ballRestrictPairing 7 L)) ∧
      ∀ x y : ℂ, 0 ≤ Ψc (ballRestrictPairing 7 L) x y)
    (hdec : ∀ L ∈ G, DecodesOnSetsBall I (decodedFamily Ψc) (Ψc (ballRestrictPairing 7 L)) 1
      (ballRestrictPairing 7 L))
    (hfin : ∀ L ∈ G, annulusGreenPotentialSup (Φμ (ballRestrictPairing 7 L)) 0 3 6 ≠ ⊤ ∧
      Φμ (ballRestrictPairing 7 L) U ≠ ⊤)
    (hEmeas : MeasurableSet (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M))
    (hCovU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ), ValidBall p →
        FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc (ballCen p) (ballCen p) (ballRad p)
          (2 * ballRad p) Set.univ (pinchOmegaGeom W Q δ) U V W T Q' Q δ M (AdmissibleRootShift 0) rootRadius
          (FirstPassS11at.decodedRootMeasure (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) γ 0 hC)
          (FirstPassS11at.decodedRootMetric (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) γ 0 hC)
          (fun L => Φμ (ballRestrictPairing 7 L)) (fun L => Ψc (ballRestrictPairing 7 L)))
    (hGrootU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ p : ℚ × ℚ × ℚ, ValidBall p →
        ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), z ∈ (Set.univ : Set ℂ) →
          ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift 0 z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
            dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)) ∈ G) :
    InsertionZeroUnitStmt.{0} γ (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M)
      U V W T Q' Q δ M := by
  have hHref : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M) q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
        (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇),
        IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q := by
    intro Ω _ P _ q hq hC' hcirc' μ' 𝔇 h𝔇 hG' _ p hp
    have hsub : closedBall (ballCen p) (ballRad p) ⊆ ball (ballCen p) (2 * ballRad p) :=
      Metric.closedBall_subset_ball (by linarith [(validBall_facts hp).1])
    have hhh := HarmonicBalls.FirstPassS11iHFdefOnGChain.ae_href_of_covariance_G hCM hB hG' hsub hEmeas
      (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
      (fun L => Φμ (ballRestrictPairing 7 L)) (fun L => Ψc (ballRestrictPairing 7 L)) G
      (HarmonicBalls.FirstPassS11iHFdefOnG.hFdef_decoded_on_G hgeo hΩ I Ψc Φμ G hmet hdec hfin)
      (hCovU Ω P hC' hcirc' hG' 𝔇 h𝔇 p hp) (hGrootU Ω P hC' hcirc' hG' p hp)
    have hset : {ω | alphaCanon γ hC' ω ∈ ballRestrictPairing 7 ⁻¹'
        decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M} =
        {ω | localModConstField γ hC' (ball (0 : ℂ) 7) ω ∈
          decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M} := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_preimage, HarmonicBalls.S11iCert.ballRestrict_alphaCanon_eq]
    have hq' : (P {ω | alphaCanon γ hC' ω ∈ ballRestrictPairing 7 ⁻¹'
        decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M}).toReal = q := by
      rw [hset]
      exact hq Ω P hC' hcirc' hG'
    rw [hq'] at hhh
    exact hhh
  exact insertionZeroUnit_of_href hγ0 hγ2 hgeo hK hR hfr hPos hNon hA10 hHref

end HarmonicBalls.FirstPassS11iInsertionZeroUnitE

#print axioms HarmonicBalls.FirstPassS11iInsertionZeroUnitE.insertionZeroUnit_decoded_on_G
