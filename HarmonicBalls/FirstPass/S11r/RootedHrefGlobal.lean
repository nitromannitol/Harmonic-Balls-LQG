import HarmonicBalls.FirstPass.S11r.RootedBallMetric
import HarmonicBalls.FirstPass.S11r.RootedCovGiven
import HarmonicBalls.FirstPass.S11r.RootedDex
import HarmonicBalls.FirstPass.S11r.GlobalG
import HarmonicBalls.FirstPass.S11i.HFdefOnG
import HarmonicBalls.FirstPass.S11i.OnGTermwise
import HarmonicBalls.FirstPass.S11i.Step8CalibrationCanonical

/-!
# The rooted `href` with the global decoders on the agreement set

Two layers.

* `href_ballMetric_global_of_inputs` (layer A): the `href` field of one whole-plane insertion-zero model `(P, hC, hcirc, μ)`
  for the global canonical decoders `D` (`CanonDecoderData γ ξ γ`, frozen clause 4) on the agreement set
  `G = globalG D Ostar U V W T Q' Q η M E` (GlobalG.lean). The rooted membership `hGroot` is derived from
  `hGroot_of_wholePlane` (OnGTermwise.lean), the certificate identity `hFdefG` by construction, the regularity from `D.regular_G`,
  and the last step is `ae_href_of_covariance_G` (HFdefOnG.lean). The almost sure membership `hGa` of the canonical field in `G`
  and the covariance set `G0` are inputs of this layer.

* `hHref_of_global` (layer B): the exact named `hHref` of `insertionZeroUnit_of_href` (InsertionZeroUnitE.lean:52), for an
  arbitrary coding set `E` with the Lemma 11.12 a.s. equivalence `hEEU` (`pinchLocalCertificate_canonical_of_inputs`, Step8CalibrationCanonical.lean). For an insertion-zero model `(P, hC', hcirc', μ')` the insertion-`γ` model needed for `hEEU`
  and for `canonG0_of_model` is built on the field translated by `z = 0`, which has the same canonical field
  (`alphaCanon_translatedPairing_zero`). The insertion-`γ` measure comes from the universal existence `hνexU` (`LQGMeasureExistence`,
  Proposed/LQG.lean:68), the insertion-`γ` metric from `exists_isLQGMetricOfField_translatedPairing_derived`.

Universal inputs of layer B are binders with their Prop named (no new Prop is introduced here).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
open HarmonicBalls.FirstPassS11rRootedBallMetric
open HarmonicBalls.FirstPassS11iStep8PhysExists FirstPassS11i HarmonicBalls.S11iCert
open HarmonicBalls.FirstPassS11rGlobalG HarmonicBalls.FirstPassS11rFrozenCanonDecoders

namespace HarmonicBalls.FirstPassS11rRootedHrefGlobal

/-- The translated field at `z = 0` has the same canonical field: the constant correction
`hcirc ω 1 0 * ∫ φ` of `translatedPairing` vanishes on mean-zero test functions. -/
theorem alphaCanon_translatedPairing_zero {Ω : Type} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    alphaCanon α (translatedPairing hC hcirc 0) ω = alphaCanon α hC ω := by
  funext i
  simp [alphaCanon, fieldPairing, translatedPairing, i.2.2]

/-- The normalized kernel `ballKernel = discNormalizedKernel kernelF` inherits the rooted kernel clause of `kernelF`
(`kernelF_clause`): the normalizing factor `(1 + κF(ball))⁻¹` is a positive finite scalar, since `kernelF` is a finite kernel. -/
theorem ballKernel_clause {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          ((ballKernel hγ0 hγ2 hK p) (campbellReferenceObs γ α (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).restrict
              (ball (ballCen p) (2 * ballRad p)) =
            ENNReal.ofReal a • (μz ω).restrict (ball (ballCen p) (2 * ballRad p)) := by
  intro α hα Ω _ P _ hC hcirc hG
  have := kernelF_isFiniteKernel hγ0 hγ2 hK p hp
  have hB : MeasurableSet (ball (ballCen p) (2 * ballRad p)) := measurableSet_ball
  filter_upwards [kernelF_clause hγ0 hγ2 hK p hp α hα Ω P hC hcirc hG] with z hz μz hμz
  filter_upwards [hz μz hμz] with ω hω
  obtain ⟨a, ha, h⟩ := hω
  set L := (campbellReferenceObs γ α (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 with hL
  have ht : kernelF hγ0 hγ2 hK p L (ball (ballCen p) (2 * ballRad p)) ≠ ⊤ := measure_ne_top _ _
  set s := (kernelF hγ0 hγ2 hK p L (ball (ballCen p) (2 * ballRad p))).toReal with hs_def
  have hs0 : 0 < 1 + s := by positivity
  refine ⟨a / (1 + s), div_pos ha hs0, ?_⟩
  change ((1 + kernelF hγ0 hγ2 hK p L (ball (ballCen p) (2 * ballRad p)))⁻¹ •
      (kernelF hγ0 hγ2 hK p L).restrict (ball (ballCen p) (2 * ballRad p))).restrict
        (ball (ballCen p) (2 * ballRad p)) = _
  rw [Measure.restrict_smul, Measure.restrict_restrict hB, Set.inter_self, h, smul_smul]
  congr 1
  have e : 1 + kernelF hγ0 hγ2 hK p L (ball (ballCen p) (2 * ballRad p)) = ENNReal.ofReal (1 + s) := by
    rw [hs_def, ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal ht]
  rw [e, ← ENNReal.ofReal_inv_of_pos hs0, ← ENNReal.ofReal_mul (inv_nonneg.mpr hs0.le)]
  congr 1
  ring

/-- **Layer A: the `href` field for the global decoders on `G`, for one whole-plane insertion-zero model.** -/
theorem href_ballMetric_global_of_inputs {γ ξ q η M : ℝ}
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p)
    {E : Set Step8Code} (hE : MeasurableSet E)
    (Ostar U V W T Q' Q : Set ℂ)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hη : 0 < η)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hUm : MeasurableSet U)
    (D : CanonDecoderData γ ξ γ)
    (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ globalG D Ostar U V W T Q' Q η M E)
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      D.K (dilOp L) = ENNReal.ofReal a • (D.K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
      ∀ u v : ℂ, D.d (dilOp L) (u, v) = b * D.d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v))
    (hPos : LQGMeasureSquarePositiveFrozen.{0})
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0}) (hLenFr : LQGMetricLengthUnivFrozen.{0})
    (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{0}) (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{0}) (hXi : LQGMetricExponentPositive)
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hq : q = (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' E}).toReal) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Ostar U V W T Q' Q η M) q := by
  obtain ⟨hr, hcl, hout, h0'⟩ := validBall_facts hp
  have : IsFiniteKernel (kernelF hγ0 hγ2 hK p) := kernelF_isFiniteKernel hγ0 hγ2 hK p hp
  have hGm : MeasurableSet (globalG D Ostar U V W T Q' Q η M E) :=
    measurableSet_globalG D hOstar h0 hsph hUm hη hE
  have hFdefG : ∀ L ∈ globalG D Ostar U V W T Q' Q η M E,
      FirstPassS11i.CertificateEvent (D.K L) (fun x y => D.d L (x, y)) Ostar U V W T Q' Q η M 1 0 ↔
        ballRestrictPairing 7 L ∈ E :=
    fun L hL => hFdefG_globalG D (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T) (Q' := Q') (Q := Q)
      (η := η) (M := M) (E := E) L hL
  have hGreg : ∀ L ∈ globalG D Ostar U V W T Q' Q η M E, IsEuclideanLengthMetric (fun x y => D.d L (x, y)) :=
    fun L hL => (D.regular_G L hL.1).2
  have hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => D.d L (x, y) :=
    fun x y => D.measurable_dd x y
  have hDμ : Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => D.K L := D.measurable_K
  have hLenC := hLenC_of_dilation_data hCM γ 0 hG
    (fun z => isWholePlaneGFF_translatedPairing (fun Q C K => HarmonicBalls.wholePlaneGFFAffineInvariance_derived Q C K) hG z)
    (c₁ := ballCen p) (r₁ := ballRad p) (ball (ballCen p) (ballRad p)) (globalG D Ostar U V W T Q' Q η M E) hGm hGa
    (fun L x y => D.d L (x, y)) hGreg
  have hEx : LQGMeasureExistence P γ 0 hC hcirc := fun _ _ _ _ => ⟨μ, hμ⟩
  have hCov := FirstPassS11ai.rootedCertificateEventualCovarianceStmt_of_given_families hCM hγ0 hγ2 (lqgQ_pos hγ0) h𝔇
    hG (c₁ := ballCen p) (c₂ := ballCen p) (r₁ := ballRad p) (r₂ := 2 * ballRad p) (hr₂ := by linarith)
      hcl h0' hout Set.univ Ostar U V W T Q' Q η M hCont hU (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ)
    (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) (ballKernel_clause hγ0 hγ2 hK p hp) (metricCont_clause20 hγ0 hγ2 hR 𝔇 h𝔇 p hp)
    (fun L => D.K L) (fun L x y => D.d L (x, y)) hDμ hDd D.ident hPos (globalG D Ostar U V W T Q' Q η M E) hGm hGa
    hGreg G0 hG0 hG0a hinv hstep hEx hEx hA10 hProf hLenFr hFieldFr hRootFr hUax hR hK hXi hComp hCC hνex (by filter_upwards [hLenC, ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball] with z hz hzb _; exact hz hzb)
  have hae := ae_ballMetric_decodedRoot_eq hG hfr hγ0 hγ2 (lqgQ_pos hγ0) hR h𝔇 p hp
  have hCov' := rootedCert_congr_dR
    (dR' := FirstPassS11at.decodedRootMetric (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) γ 0 hC) hCov
    (by filter_upwards [hae] with z hz; filter_upwards [hz] with ω hω; exact hω.symm)
  have hGroot := HarmonicBalls.FirstPassS11iOnGTermwise.hGroot_of_wholePlane hCM γ hG hGm hGa (ballCen p) (ballRad p) 0
  have hnull := HarmonicBalls.FirstPassS11iHFdefOnGChain.ae_href_of_covariance_G hCM hB hG hcl hE
    (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Ostar U V W T Q' Q η M
    (fun L => D.K L) (fun L x y => D.d L (x, y)) (globalG D Ostar U V W T Q' Q η M E) hFdefG hCov' hGroot
  rw [hq]
  exact hnull

/-- **Layer B: the named `hHref` of `insertionZeroUnit_of_href` (InsertionZeroUnitE.lean:52), for the coding set `E`.**
The insertion-`γ` model needed for the event identity and for `canonG0_of_model` is built on the field translated by `0`,
which has the same canonical field (`alphaCanon_translatedPairing_zero`). Universal inputs (binders): `hνexU`
(`LQGMeasureExistence`, Proposed/LQG.lean:68), `hEEU` (the a.s. event equivalence of `pinchLocalCertificate_canonical_of_inputs`,
S11i/Step8CalibrationCanonical.lean:36, for insertion-`γ` models), `hCCU` (`LQGMeasureCoordChange` of the translated fields),
`hA10U` (`DMSLemmaA10WholePlaneMarkedSub`), and the frozen binders of `insertionZeroUnit_of_href`. -/
theorem hHref_of_global {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (hProf : HarmonicBalls.LQGMeasureOfProfileMeasurableFrozen.{0})
    (hLenFr : HarmonicBalls.LQGMetricLengthUnivFrozen.{0})
    (hFieldFr : HarmonicBalls.LQGMetricFieldAxiomsUnivFrozen.{0})
    (hRootFr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hUax : HarmonicBalls.LQGMetricSatisfiesAxiomsUnivFrozen.{0}) (hXi : HarmonicBalls.LQGMetricExponentPositive)
    (hComp : HarmonicBalls.WeylMetricCompositionContinuousOuterFrozen)
    (D : CanonDecoderData γ (lqgXi γ) γ)
    (hE : MeasurableSet E)
    (hνexU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.LQGMeasureExistence P γ γ hC hcirc)
    (hEEU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (Dm : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC Dm →
      ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
        CertificateEvent (μ ω) (Dm ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    (hCCU : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ),
      LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hA10U : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
        (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q := by
  intro Ω _ P _ q hq hC' hcirc' μ' 𝔇 h𝔇 hG hμ p hp
  have hγQ : γ < lqgQ γ := lt_lqgQ_of_mem_Ioo hγ0 hγ2
  have hT0 : IsWholePlaneGFF P (S11c.translatedPairing hC' hcirc' 0) (S11c.translatedCircle hcirc' 0) :=
    isWholePlaneGFF_translatedPairing (fun Q C K => HarmonicBalls.wholePlaneGFFAffineInvariance_derived Q C K) hG 0
  obtain ⟨Dγ, hDγ⟩ := HarmonicBalls.exists_isLQGMetricOfField_translatedPairing_derived hγ0 hγ2 hG h𝔇 hFieldFr 0
  obtain ⟨μγ, hμγ⟩ := hνexU Ω P (S11c.translatedPairing hC' hcirc' 0) (S11c.translatedCircle hcirc' 0) hT0 hγ0 hγ2 hγQ
  have hEv := hEEU Ω P (S11c.translatedPairing hC' hcirc' 0) (S11c.translatedCircle hcirc' 0) μγ Dγ hT0 hμγ hDγ
  have hGa0 := ae_alphaCanon_mem_globalG D (Ostar := pinchOmegaGeom W Q δ) (η := δ) (M := M) (E := E) hT0 μγ Dγ
    hμγ hDγ hEv
  obtain ⟨G0, hG0, hG0a0, hinv, hstep⟩ :=
    canonG0_of_model D hγ0 hγ2 hγQ P hT0 hμγ hDγ
  have hGa : ∀ᵐ ω ∂P, alphaCanon γ hC' ω ∈ globalG D (pinchOmegaGeom W Q δ) U V W T Q' Q δ M E := by
    filter_upwards [hGa0] with ω hω
    rwa [alphaCanon_translatedPairing_zero] at hω
  have hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC' ω ∈ G0 := by
    filter_upwards [hG0a0] with ω hω
    rwa [alphaCanon_translatedPairing_zero] at hω
  have hq' : q = (P {ω | alphaCanon γ hC' ω ∈ ballRestrictPairing 7 ⁻¹' E}).toReal := by
    rw [← hq Ω P hC' hcirc' hG]
    simp only [Set.mem_preimage, ballRestrict_alphaCanon_eq]
  obtain ⟨hOpen, h0, hsph, hCont⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  exact href_ballMetric_global_of_inputs hCM hB hγ0 hγ2 hK hR hfr hG μ' hμ h𝔇 p hp hE
    (pinchOmegaGeom W Q δ) U V W T Q' Q hOpen h0 hsph hgeo.delta_pos hCont
    (hgeo.U_subset.trans (FirstPassS11ap.annulus_subset_closedBall' 0 1 2 7 (by norm_num)))
    hgeo.isOpen_U.measurableSet D hGa G0 hG0 hG0a
    hinv hstep hPos (fun μ'' => HarmonicBalls.dmsA10Marked_of_sub P γ hC' hcirc' μ'' (hA10U Ω P hC' hcirc' μ'' ) hγ0 hγ2)
    hProf hLenFr hFieldFr hRootFr hUax hXi hComp (fun z => hCCU Ω P hC' hcirc' z)
    (fun z => hνexU Ω P (S11c.translatedPairing hC' hcirc' z) (S11c.translatedCircle hcirc' z)) hq'

end HarmonicBalls.FirstPassS11rRootedHrefGlobal

