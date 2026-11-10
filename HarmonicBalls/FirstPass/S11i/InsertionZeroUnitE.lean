import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDoubled
import HarmonicBalls.FirstPass.S11af
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.FirstPass.S11i.HFdefOnG
import HarmonicBalls.FirstPass.S11i.CertificateCanonical
import HarmonicBalls.FirstPass.S11i.OnGTermwise
import HarmonicBalls.FirstPass.S11r.GlobalG
import HarmonicBalls.FirstPass.S11s.B1Covariance
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11b

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

/-! ### Global-decoder variant (operator task fp-S11i-insertionZeroUnit-onG).
The rooted bridge uses the global canonical decoders `D.K`, `D.d` of the frozen package `CanonDecoderData`
(S11r/FrozenCanonDecoders.lean:31), not the local `Φμ`, `Ψc`, which only define the coding set `E`.
The old theorems above are kept unchanged. -/

/-- Ball-root decoded measure: the local kernel `κ_p` at the root `z`, with observation at insertion `α₀ = 0`. -/
noncomputable def ballRootMu {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (p : ℚ × ℚ × ℚ) {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : Measure ℂ :=
  FirstPassS11at.decodedRootMeasure (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) γ 0 hC z ω

/-- Ball-root decoded metric: the local metric decoder `𝔇_p` at the root `z`, with observation at `α₀ = 0`. -/
noncomputable def ballRootMet {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ)
    {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  FirstPassS11at.decodedRootMetric (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) γ 0 hC z ω

/-- The pushforward of the ball-root measure under the translation by `-z` (the `μ0` of the covariance transfer). -/
theorem map_sub_sub_neg_eq (μ : Measure ℂ) (z : ℂ) :
    (μ.map (fun w : ℂ => w - z)).map (fun w : ℂ => w - -z) = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- **Global-decoder variant of `insertionZeroUnit_decoded_on_G`.** The coding set `E` is as before (defined by the
local decoders `Ψc`, `Φμ`). The agreement set is `G = globalG D … E` (S11r/GlobalG.lean:40) of the frozen global
decoders `D`. Its membership is the exact certificate identity (`hFdefG_globalG`), its regularity comes from
`D.regular_G`, its measurability from `measurableSet_globalG`. Rooted membership `hGroot` is discharged by
`hGroot_of_wholePlane`, and the covariance `hCovU` is the covariance transfer with the global decoders
(`rootedCertificateEventualCovarianceStmt_of_transfer`, with `B1_covariance` for `G0`).

Named inputs that are NOT in the frozen package (stated exactly, not assumed by any existence claim):
* `hLQG`: for every whole-plane model, a γ-insertion LQG measure `μ` and a metric `Dm` at `ξ = lqgXi γ` with the
  almost-sure physical-event equivalence of Lemma 11.12 step 2 (`localModConstField ∈ E ↔ CertificateEvent (μ ω) (Dm ω)`).
  The existence of `μ` is the Proposed `LQGMeasureExistence` (Proposed/LQG.lean:68) in the case `α₀ = γ`. The existence
  of `Dm` at exponent `lqgXi γ` is NOT in Proposed (`LQGMetricExistenceUniqueness`, Proposed/LQG.lean:175, gives some `ξ`).
* `hDecInt`, `hMass`: the decoded pair for the global decoders on the ball decoders (the two inputs of
  `rootedCertificateEventualCovarianceStmt_of_transfer`, S11at.lean:480).
Not needed by this route: `hmet`, `hdec`, `hfin` (the local G-data), since `G` carries its own certificate identity. -/
theorem insertionZeroUnit_globalOnG {γ δ M : ℝ} {U V W T Q' Q : Set ℂ}
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
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (D : HarmonicBalls.FirstPassS11rFrozenCanonDecoders.CanonDecoderData γ (lqgXi γ) γ)
    (I : HarmonicBalls.S11am.PinchCountSets V W T Q' Q δ)
    (Ψc : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ → ℂ → ℝ)
    (Φμ : ModConstTestPairings (ball (0 : ℂ) 7) → Measure ℂ)
    (hEmeas : MeasurableSet (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M))
    (hLQG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∃ (μ : Ω → Measure ℂ) (Dm : Ω → ℂ → ℂ → ℝ), IsLQGMeasureOfField P γ γ hcirc μ ∧
        IsLQGMetricOfField P γ (lqgXi γ) γ hC Dm ∧
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈
            decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M ↔
          FirstPassS11i.CertificateEvent (μ ω) (Dm ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    (hDecInt : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ),
        ValidBall p → ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), z ∈ (Set.univ : Set ℂ) →
          ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift 0 z b u → ∀ᵐ ω ∂P, ∃ ρ r β : ℝ, 0 < ρ ∧ 0 < r ∧ 0 < β ∧
            closedBall (0 : ℂ) (2 * ρ) ⊆ ball 0 b ∩ ball 0 (rootRadius z) ∩
              ((fun x : ℂ => x + z) ⁻¹' ball (ballCen p) (2 * ballRad p)) ∧
            ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
              ballRootMet hγ0 hγ2 hR 𝔇 h𝔇 p hC z ω (x + z) (y + z) =
                β * (internalMetric (fun a b => D.d (FirstPassS11at.shiftedCanon γ hC hcirc z u ω) (a, b))
                  (ball 0 (2 * ρ)) x y).toReal)
    (hMass : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (_h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ),
        ValidBall p → ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), z ∈ (Set.univ : Set ℂ) →
          ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift 0 z b u → ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
            ((ballRootMu hγ0 hγ2 hK p hC z ω).map (fun w : ℂ => w - z)).restrict
                (closedBall 0 (7 * FirstPassS11ah.certScale n)) =
              (ENNReal.ofReal a • D.K (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)).restrict
                (closedBall 0 (7 * FirstPassS11ah.certScale n))) :
    InsertionZeroUnitStmt.{0} γ (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M)
      U V W T Q' Q δ M := by
  classical
  obtain ⟨hOstar, h0, hsph, hCC⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  have hU7 : U ⊆ closedBall (0 : ℂ) 7 := fun z hz => by
    have h2 : dist z 0 < 2 := (hgeo.U_subset hz).1
    exact mem_closedBall.2 (by linarith)
  have hGm := FirstPassS11rGlobalG.measurableSet_globalG (Ostar := pinchOmegaGeom W Q δ) (U := U) (V := V)
    (W := W) (T := T) (Q' := Q') (Q := Q) (η := δ) (M := M) D hOstar h0 hsph hgeo.isOpen_U.measurableSet
    hgeo.delta_pos hEmeas
  have hGreg : ∀ L ∈ FirstPassS11rGlobalG.globalG D (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
      (decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M),
      IsEuclideanLengthMetric (fun x y => D.d L (x, y)) :=
    fun L hL => (D.regular_G L hL.1).2
  have hAdmReg : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift 0 z b u →
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 :=
    fun _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hα : γ < lqgQ γ := lt_lqgQ_self hγ0 hγ2
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
    obtain ⟨μm, Dm, hμm, hDm, hEv⟩ := hLQG Ω P hC' hcirc' hG'
    have hGa := FirstPassS11rGlobalG.ae_alphaCanon_mem_globalG D hG' μm Dm hμm hDm hEv
    have hGroot := FirstPassS11iOnGTermwise.hGroot_of_wholePlane hCM γ hG' hGm hGa (ballCen p) (ballRad p) 0
    obtain ⟨G0, hG0, hG0a, hinv, hstep⟩ := HarmonicBalls.B1_covariance hγ0 hγ2 hα P hG' hμm hDm
      D.K D.d D.measurable_d D.finiteOnCompacts_K D.ident D.G D.measurableSet_G
      (D.ae_mem_G Ω P hC' hcirc' hG') D.regular_G
    have hCovU := FirstPassS11at.rootedCertificateEventualCovarianceStmt_of_transfer hCM hC' hcirc' hG'
      (fun z => HarmonicBalls.S11c.isWholePlaneGFF_translate hG' z)
      (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) Set.univ (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
      hCC hU7 (AdmissibleRootShift 0) hAdmReg rootRadius
      (fun z ω => (ballRootMu hγ0 hγ2 hK p hC' z ω).map (fun w : ℂ => w - z))
      (fun z ω => ballRootMu hγ0 hγ2 hK p hC' z ω)
      (fun z ω x y => ballRootMet hγ0 hγ2 hR 𝔇 h𝔇 p hC' z ω (x + z) (y + z))
      (fun z ω => ballRootMet hγ0 hγ2 hR 𝔇 h𝔇 p hC' z ω) (fun L => D.K L) (fun L x y => D.d L (x, y))
      _ hGm hGa hGreg G0 hG0 hG0a hinv hstep (fun z ω => (map_sub_sub_neg_eq _ z).symm)
      (fun z ω => by funext x y; simp) (hDecInt Ω P hC' hcirc' hG' 𝔇 h𝔇 p hp) (hMass Ω P hC' hcirc' hG' 𝔇 h𝔇 p hp)
    have hsub : closedBall (ballCen p) (ballRad p) ⊆ ball (ballCen p) (2 * ballRad p) :=
      Metric.closedBall_subset_ball (by linarith [(validBall_facts hp).1])
    have hhh := FirstPassS11iHFdefOnGChain.ae_href_of_covariance_G hCM hB hG' hsub hEmeas
      (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
      (fun L => D.K L) (fun L x y => D.d L (x, y)) _ (FirstPassS11rGlobalG.hFdefG_globalG D) hCovU hGroot
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
