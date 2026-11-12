import HarmonicBalls.FirstPass.Phase2.Step8RootedModelCert
import HarmonicBalls.FirstPass.Phase2.Step8OriginFrequencyFixedMetric

/-!
# Step 8 of Lemma 11.13: the reference-null field `hHref` for one fixed LQG metric

Fix an LQG metric `𝔇₀` (`IsLQGMetric γ ξ 𝔇₀`). This file gives the forms of `Phase2/Step8HrefOfModel.lean` and
`Phase2/Step8RootedModelCert.lean` in which every model metric is the Weyl scaling of `𝔇₀`:

* `RootedModelCertificateFixedMetricStmt`: the model certificate at the root, with the metric of the translated model
  equal to the Weyl scaling of `𝔇₀` at the translated field (by `-γ log|·|`);
* `rootedTermwise_of_modelCertificate_fixedMetric`, `href_of_modelCertificate_fixedMetric`,
  `hHref_of_modelCertificate_fixedMetric`: the termwise identification and the reference-null field, from the
  fixed-metric seed and the fixed-metric model certificate;
* `rootedModelCertificate_ballDecoders_fixedMetric`, `hPhys_ballDecoders_fixedMetric`: the fixed-metric model
  certificate for the ball decoders of `𝔇₀`;
* `hHref_of_seed_fixedMetric`: the reference-null field for the ball decoders of `𝔇₀` from the fixed-metric seed.

The seed hypothesis is the one produced for a fixed metric by `pinchLocalCertificate_seed_fixedMetric`
(`Phase2/Step8SeedFixedMetric.lean`), without the uniqueness of the LQG metric (GM21). The translated model of the
root keeps the metric `𝔇₀` (`fixedMetric_centredWeylMetric`), as the half-scale pullback does
(`ae_fixedMetric_affinePullback`, `Phase2/Step8OriginFrequencyFixedMetric.lean`), so the proofs are those of the
forms for all metrics, with the metric fixed.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassPhase2Step8HrefFixedMetric

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassPhase2Step8OriginFrequency HarmonicBalls.FirstPassPhase2Step8OriginFrequencyFixedMetric
open HarmonicBalls.FirstPassPhase2Step8HrefOfModel HarmonicBalls.FirstPassPhase2Step8RootedModelCert
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
open HarmonicBalls.FirstPassS11rRootedBallMetric HarmonicBalls.FirstPassS11rRootedHrefGlobal

/-- **The model certificate at the root, for a fixed LQG metric `𝔇₀`.** For Lebesgue-almost every root `z` of
`B_{r₁}(c₁)` there are an LQG measure `μT` of the field translated by `z` (insertion `γ`) and a metric `DT` which is
almost surely the Weyl scaling of `𝔇₀` at the translated field by `-γ log|·|`, such that almost surely, for all large
`n`, the decoded local certificate at radius `certScale n` about `z` holds if and only if the certificate of
`(μT, DT)` at radius `certScale n` about `0` holds. -/
def RootedModelCertificateFixedMetricStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ (μT : Ω → Measure ℂ) (DT : Ω → ℂ → ℂ → ℝ),
    IsLQGMeasureOfField P γ γ (translatedCircle hcirc z) μT ∧
    (∀ᵐ ω ∂P, ∀ u v, 0 ≤ DT ω u v ∧ ENNReal.ofReal (DT ω u v) =
      weylScaling (𝔇₀ (translatedPairing hC hcirc z ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) ∧
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (FirstPassS11i.CertificateEvent (κ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2)
          (m (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2) Ostar U V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μT ω) (DT ω) Ostar U V W T Q' Q η M (certScale n) 0)

/-- **The centred Weyl metric is the Weyl scaling of the fixed metric.** Under Fact 2.2 (`hAx`), the centred Weyl
metric of `𝔇` at the root `z` is almost surely nonnegative, equal to the Weyl scaling of `𝔇` at the field translated
by `z` (by `-γ log|·|`), and a Euclidean length metric. -/
theorem fixedMetric_centredWeylMetric (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (z : ℂ) :
    (∀ᵐ ω ∂P, ∀ u v, 0 ≤ centredWeylMetric 𝔇 ξ γ hC hcirc z ω u v ∧
      ENNReal.ofReal (centredWeylMetric 𝔇 ξ γ hC hcirc z ω u v) =
        weylScaling (𝔇 (translatedPairing hC hcirc z ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) ∧
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) := by
  have hfin := hAx Ω P γ ξ γ (translatedPairing hC hcirc z) (translatedCircle hcirc z)
    (isWholePlaneGFF_translate hG z) hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) 𝔇 h𝔇
  refine ⟨?_, ?_⟩
  · filter_upwards [hfin.1] with ω hω
    intro u v
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hω.1 u v).ne⟩
  · filter_upwards [hfin.1] with ω hω
    exact hω.2

/-- **Termwise identification at the insertion `0`, from the fixed-metric seed and the fixed-metric model certificate
at the root.** -/
theorem rootedTermwise_of_modelCertificate_fixedMetric {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ}
    {η M : ℝ} {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ ξ 𝔇₀)
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (A : Set ℂ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hPhys : RootedModelCertificateFixedMetricStmt P γ ξ 𝔇₀ hC hcirc c₁ c₂ r₁ r₂ κ m Ostar U V W T Q' Q η M) :
    RootedCertificateTermwiseIdentificationStmt P γ 0 hC hcirc c₁ c₂ r₁ r₂ A E κ m Ostar U V W T Q' Q η M := by
  classical
  set S : Set (ModConstTestPairings (univ : Set ℂ)) := canonRestrict (ball (0 : ℂ) 7) ⁻¹' E with hSdef
  have hS : MeasurableSet S := measurable_canonRestrict _ hE
  have h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (alphaCanon γ hC ω ∈ S ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0) :=
    fun Ω _ P hC hcirc μ D hG hμ hD => hEq Ω P hC hcirc μ D hG hμ hD
  filter_upwards [hPhys, ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball]
    with z hz hzB _ b u hb _ _ _ _ _ hu0
  obtain ⟨μT, DT, hμT, hDT, hev⟩ := hz
  have hGT : IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) :=
    isWholePlaneGFF_translatedPairing
      (fun Q C K => HarmonicBalls.wholePlaneGFFAffineInvariance_derived Q C K) hG z
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, (dilOp^[n] (alphaCanon γ (translatedPairing hC hcirc z) ω) ∈ S ↔
      FirstPassS11i.CertificateEvent (μT ω) (DT ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0) :=
    ae_all_iff.2 fun n => ae_iterate_mem_iff_certificate_fixedMetric hγ h𝔇₀ hS h0 n Ω P _ _ μT DT hGT hμT hDT
  have hzD : z ∈ ball c₂ r₂ := hsub (ball_subset_closedBall hzB)
  have hb' : ∀ᶠ n : ℕ in atTop, 7 / (2 : ℝ) ^ n < b :=
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).eventually (gt_mem_nhds hb)
  filter_upwards [hev, hall] with ω hω hω'
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hω.and ((eventually_closedBall_cutRadius_subset hzD).and hb'))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hcert, hcut, hbn⟩ := hn₀ n hn
  have hloc := ballRestrict_dilOp_iterate_addFun_eq γ (T := translatedPairing hC hcirc z ω) hu0 hbn
  have key : ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (translatedPairing hC hcirc z ω))) ∈ E ↔
      FirstPassS11i.CertificateEvent (μT ω) (DT ω) Ostar U V W T Q' Q η M (certScale n) 0 := hω' n
  have hcut' : closedBall (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).1 (cutRadius n) ⊆ ball c₂ r₂ := hcut
  simp only [localCertSeq, localCert, hcut', ↓reduceIte, Set.indicator_apply, Set.mem_preimage, hloc]
  exact if_congr (hcert.trans key.symm) rfl rfl

/-- **The reference-null field from the fixed-metric model certificate at the root.** For a whole-plane model,
decoders `κ`, `m` on `B_{r₂}(c₂) ⊇ closedBall c₁ r₁`, and a coding event `E` with common probability `q`, the
fixed-metric seed `hEq` and the fixed-metric model certificate at the root give: for Lebesgue-almost every
`z ∈ B_{r₁}(c₁)`, almost surely the Campbell reference observation at `z` is not in the bad window set of the decoded
local certificates at level `q`. -/
theorem href_of_modelCertificate_fixedMetric {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ ξ 𝔇₀)
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {q : ℝ} (hq : CommonProb.{0} γ E q)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hPhys : RootedModelCertificateFixedMetricStmt P γ ξ 𝔇₀ hC hcirc c₁ c₂ r₁ r₂ κ m Ostar U V W T Q' Q η M) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U V W T Q' Q η M) q := by
  have hT := rootedTermwise_of_modelCertificate_fixedMetric hγ h𝔇₀ hE hEq hG hsub Set.univ κ m hPhys
  have h := FirstPassS11iStep8Href.ae_href_of_termwise
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived birkhoffPointwiseErgodic_derived hG Set.univ hE κ m
    Ostar U V W T Q' Q η M hT
  have hq' : q = (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' E}).toReal :=
    (hq Ω P hC hcirc hG).symm
  rw [hq']
  rw [ae_restrict_iff' measurableSet_ball] at h
  exact h.mono fun z hz hzB => hz hzB (mem_univ z)

/-- **The field `hHref` for the ball decoders of a fixed LQG metric `𝔇₀`, from the fixed-metric seed and the
fixed-metric model certificate at the root.** No canonical decoder and no uniqueness of the LQG metric are used. -/
theorem hHref_of_modelCertificate_fixedMetric {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇₀)
    (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    (hPhys : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          RootedModelCertificateFixedMetricStmt P γ (lqgXi γ) 𝔇₀ hC' hcirc' (ballCen p) (ballCen p) (ballRad p)
            (2 * ballRad p) (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' → HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q := by
  intro Ω _ P _ q hq hC' hcirc' _ hG _ p hp
  exact href_of_modelCertificate_fixedMetric hγ0 h𝔇₀ hE hEq hq hG (validBall_facts hp).2.1 _ _
    (hPhys Ω P hC' hcirc' hG p hp)

/-- **The fixed-metric model certificate at the root for the ball decoders of `𝔇` (Lemma 11.13, Step 8).** The form
of `rootedModelCertificate_ballDecoders` in which the metric of the translated model is recorded as the Weyl scaling
of `𝔇` itself (`fixedMetric_centredWeylMetric`). Inputs: the frozen decoder statements `hK`, `hR`, the rooted
continuity `hfr` and Fact 2.2 (`hAx`). -/
theorem rootedModelCertificate_ballDecoders_fixedMetric {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) :
    RootedModelCertificateFixedMetricStmt P γ (lqgXi γ) 𝔇 hC hcirc (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)
      (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Ostar U V W T Q' Q η M := by
  obtain ⟨-, hcl, hout, h0⟩ := validBall_facts hp
  have hXi : LQGMetricExponentPositive :=
    FirstPassS11iFinal11_13.lqgMetricExponentPositive_derived wholePlaneGFFExistsFrozen_derived'.{0}
  have hκ := ballKernel_clause hγ0 hγ2 hK p hp 0 (lqgQ_pos hγ0) Ω P hC hcirc hG
  have hm := metricCont_clause20 hγ0 hγ2 hR 𝔇 h𝔇 p hp 0 (lqgQ_pos hγ0) Ω P hC hcirc hG
  have hbm := ae_ballMetric_decodedRoot_eq (α₀ := 0) hG hfr hγ0 hγ2 (lqgQ_pos hγ0) hR h𝔇 p hp
  filter_upwards [hκ, hm, hbm, ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball]
    with z hzκ hzm hzb hz
  have hzB : z ∈ ball (ballCen p) (2 * ballRad p) := hcl (ball_subset_closedBall hz)
  have hz0 : z ≠ 0 := fun h => h0 (h ▸ ball_subset_closedBall hzB)
  have hB1 : ball (ballCen p) (2 * ballRad p) ⊆ ball (0 : ℂ) 1 := ball_subset_closedBall.trans hout
  obtain ⟨ν, hν⟩ := lqgMeasureExistence_derived P γ γ (translatedPairing hC hcirc z) (translatedCircle hcirc z)
    (isWholePlaneGFF_translate hG z) hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2)
  obtain ⟨hDT, hDu⟩ := fixedMetric_centredWeylMetric hAx hγ0 hγ2 hG h𝔇 z
  refine ⟨ν, centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z, hν, hDT, ?_⟩
  obtain ⟨r₀, hr₀, hr₀B⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ closedBall z r₀ ⊆ ball (ballCen p) (2 * ballRad p) := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 isOpen_ball z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  have hmem : ∀ u ∈ closedBall (0 : ℂ) r₀, u + z ∈ ball (ballCen p) (2 * ballRad p) := fun u hu =>
    hr₀B (by simpa [mem_closedBall, dist_eq_norm] using hu)
  -- the decoded metric near the root
  have hT := ae_rootedWeylMetric_internalMetric_translate hγ0 hγ2 hout hG h𝔇 hXi hAx
    FirstPassS11iFinal11_13.lqgMetricSatisfiesAxiomsUnivFrozen_zero lqgMetricLengthUniv_derived.{0} hfr
    weylMetricCompositionContinuousOuter_derived hz0
  have hDecInt : ∀ᵐ ω ∂P, ∃ (W₀ : Set ℂ) (r β : ℝ), IsOpen W₀ ∧ (0 : ℂ) ∈ W₀ ∧ 0 < r ∧ 0 < β ∧
      ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
        ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z) =
          β * (internalMetric (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z ω) W₀ x y).toReal := by
    filter_upwards [hzm, hzb, hT] with ω hωm hωb hωT
    obtain ⟨b, hb, hbq⟩ := hωm
    refine ⟨(fun u => u + z) ⁻¹' ball (ballCen p) (2 * ballRad p), r₀, b * Real.exp (lqgXi γ * hcirc ω 1 z),
      isOpen_ball.preimage (continuous_id.add continuous_const), by simpa using hzB, hr₀,
      mul_pos hb (Real.exp_pos _), fun x hx y hy => ?_⟩
    have hq : (x + z, y + z) ∈ ball (ballCen p) (2 * ballRad p) ×ˢ ball (ballCen p) (2 * ballRad p) := ⟨hmem x hx, hmem y hy⟩
    have e1 : ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z) =
        metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 ⟨(x + z, y + z), hq⟩ := by
      have h1 := congrFun (congrFun hωb (x + z)) (y + z)
      simp only [FirstPassS11at.decodedRootMetric] at h1
      rw [h1]
      simp only [FirstPassS11at.windowMetric, hq, ↓reduceDIte]
    have e2 : ENNReal.ofReal (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2
        ⟨(x + z, y + z), hq⟩) = ENNReal.ofReal b * (ENNReal.ofReal (Real.exp (lqgXi γ * hcirc ω 1 z)) *
          internalMetric (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z ω) ((fun u => u + z) ⁻¹' ball (ballCen p) (2 * ballRad p)) x y) := by
      rw [hbq ⟨(x + z, y + z), hq⟩]
      congr 1
      exact hωT x y (hmem x hx) (hmem y hy)
    have hnn := ballMetric_nonneg hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2
      (hmem x hx) (hmem y hy)
    rw [← ENNReal.toReal_ofReal hnn, e1, e2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_assoc]
  -- the decoded kernel near the root
  have hκz := hzκ _ (ae_isLQGLimit_rootedMax_of_translated hG z hν)
  have h7 : Tendsto (fun n : ℕ => 7 * certScale n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => certScale n) atTop (𝓝 0) := by
      simpa [certScale] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
    simpa using h1.const_mul 7
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (h7.eventually (gt_mem_nhds hr₀))
  have hMass : ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
      ((ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).map (fun w => w - z)).restrict
          (closedBall 0 (7 * certScale n)) =
        (ENNReal.ofReal a • ν ω).restrict (closedBall 0 (7 * certScale n)) := by
    filter_upwards [hκz] with ω hω
    obtain ⟨a, ha, hka⟩ := hω
    exact ⟨n₁, fun n hn => ⟨a * Real.exp (γ * hcirc ω 1 z), mul_pos ha (Real.exp_pos _),
      map_sub_restrict_closedBall_eq measurableSet_ball hB1 ha hka
        ((closedBall_subset_closedBall (hn₁ n hn).le).trans hr₀B)⟩⟩
  have hdec := FirstPassS11at.ae_eventual_certificateEvent_decoded (P := P)
    (fun ω => (ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).map (fun w => w - z)) ν
    (fun ω x y => ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z))
    (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z) Ostar U V W T Q' Q η M hCont hU hDu hDecInt hMass
  filter_upwards [hdec] with ω hω
  obtain ⟨n₀, hn₀⟩ := hω
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have htr := FirstPassS11aq.certificateEvent_translate_iff
    (ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2)
    (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2) Ostar U V W T Q' Q η M
    (certScale n) 0 z
  rw [zero_add] at htr
  exact htr.symm.trans (hn₀ n hn)

/-- **The binder `hPhys` of `hHref_of_modelCertificate_fixedMetric`**, for a buffered pinch geometry: the fixed-metric
model certificate at the root for the ball decoders of `𝔇₀`, in every whole-plane model and every valid ball. -/
theorem hPhys_ballDecoders_fixedMetric {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇₀) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          RootedModelCertificateFixedMetricStmt P γ (lqgXi γ) 𝔇₀ hC' hcirc' (ballCen p) (ballCen p) (ballRad p)
            (2 * ballRad p) (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M := by
  obtain ⟨-, -, -, hCont⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  intro Ω _ P _ hC' hcirc' hG p hp
  exact rootedModelCertificate_ballDecoders_fixedMetric hγ0 hγ2 hK hR hfr hAx hG h𝔇₀ p hp hCont
    (hgeo.U_subset.trans (FirstPassS11ap.annulus_subset_closedBall' 0 1 2 7 (by norm_num)))

/-- **The field `hHref` for the ball decoders of a fixed LQG metric `𝔇₀`, from the fixed-metric seed of
Lemma 11.12.** The binder `hPhys` of `hHref_of_modelCertificate_fixedMetric` is `hPhys_ballDecoders_fixedMetric`.
Inputs besides the seed `hEq` (produced by `pinchLocalCertificate_seed_fixedMetric` at `α = γ`): the frozen decoder
statements `hK`, `hR`, the rooted continuity `hfr` and Fact 2.2 (`hAx`). -/
theorem hHref_of_seed_fixedMetric {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇₀) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' → HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q :=
  hHref_of_modelCertificate_fixedMetric hγ0 hγ2 hK hR h𝔇₀ hE hEq
    (hPhys_ballDecoders_fixedMetric hγ0 hγ2 hgeo hK hR hfr hAx h𝔇₀)

end HarmonicBalls.FirstPassPhase2Step8HrefFixedMetric
