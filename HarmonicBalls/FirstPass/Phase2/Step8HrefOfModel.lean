import HarmonicBalls.FirstPass.S11i.InsertionZeroUnitE
import HarmonicBalls.FirstPass.S11i.Step8Href
import HarmonicBalls.FirstPass.S11i.RootedLocality
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11ai.RootedTransfer
import HarmonicBalls.FirstPass.Phase2.Step8OriginFrequency
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9

/-!
# Lemma 11.13, Step 8: the reference-null field `href` from the model certificate at the root

The named field `hHref` of `insertionZeroUnit_of_href` (`S11i/InsertionZeroUnitE.lean`) asks, for every whole-plane
model, every LQG metric `𝔇` and every valid decoder ball, that at Lebesgue-almost every root `z` the window averages of
the decoded local certificates of the Campbell reference observation at `z` converge to the common probability `q` of the
coding event `E`.

This file proves `hHref` without a canonical decoder, from two statements:
* the seed of Lemma 11.12 (`hEq`): in every insertion-`γ` model, almost surely, the field modulo constants on `B₇(0)`
  lies in `E` if and only if the certificate event holds at radius `1` about `0`;
* the model certificate at the root (`RootedModelCertificateStmt`): at Lebesgue-almost every root `z` there is an
  insertion-`γ` LQG measure and metric of the field translated by `z` whose certificate events at radii `2⁻ⁿ` about `0`
  eventually agree with the decoded local certificates of the Campbell reference observation at `z`.

At the insertion `α₀ = 0` an admissible root shift vanishes near the root, so the dilated shifted canonical field agrees
with the dilated canonical field of the translated field on `B₇(0)` for large `n`
(`ballRestrict_dilOp_iterate_addFun_eq`). The seed, iterated along the dilations
(`ae_iterate_mem_iff_certificate`), then identifies the model certificate at radius `2⁻ⁿ` with the coding event at the
`n`-th dilate, which is the termwise identification of Step 8 (`rootedTermwise_of_modelCertificate`). The window limit
is `ae_href_of_termwise` with the derived Cameron-Martin and Birkhoff inputs.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassPhase2Step8HrefOfModel

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassPhase2Step8OriginFrequency
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

/-- Pairings with test functions supported where `u` vanishes do not see the shift by `u`. -/
theorem addFunPairing_eq_of_eqOn_zero {T : (ℂ → ℝ) → ℝ} {u : ℂ → ℝ} {b : ℝ}
    (hu : ∀ w ∈ ball (0 : ℂ) b, u w = 0) {φ : ℂ → ℝ} (hφ : IsTestFunction (ball (0 : ℂ) b) φ) :
    addFunPairing T u φ = T φ := by
  have h : ∀ x, u x * φ x = 0 := by
    intro x
    by_cases hx : x ∈ ball (0 : ℂ) b
    · rw [hu x hx, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero]
  simp [addFunPairing, h]

/-- At the insertion `α₀ = 0` an admissible root shift `u` vanishes on `B_b(0)`, so for `7 / 2ⁿ < b` the `n`-th dilate of
the canonical field of `T + u` agrees with that of `T` on `B₇(0)`. -/
theorem ballRestrict_dilOp_iterate_addFun_eq (γ : ℝ) {T : (ℂ → ℝ) → ℝ} {z : ℂ} {b : ℝ} {u : ℂ → ℝ}
    (hu : ∀ w ∈ ball (0 : ℂ) b, u w = -0 * Real.log ‖z + w‖) {n : ℕ} (hn : 7 / 2 ^ n < b) :
    ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing T u))) =
      ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ T)) :=
  ballRestrict_dilOp_iterate_eq γ
    (fun _ hφ _ => addFunPairing_eq_of_eqOn_zero (fun w hw => by simpa using hu w hw) hφ) n hn

/-- **The model certificate at the root (Lemma 11.13, Step 8, local transfer at the insertion `0`).** For
Lebesgue-almost every root `z ∈ B_{r₁}(c₁)` there are an LQG measure `μT` (insertion `γ`) and an LQG metric `DT`
(insertion `γ`) of the whole-plane field translated by `z` such that, almost surely, eventually in `n`, the decoded
local certificate (decoders `κ`, `m` on `B_{r₂}(c₂)`) of the Campbell reference observation at `z` at radius `2⁻ⁿ`
about `z` holds if and only if the certificate of `(μT, DT)` at radius `2⁻ⁿ` about `0` holds. -/
def RootedModelCertificateStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ (μT : Ω → Measure ℂ) (DT : Ω → ℂ → ℂ → ℝ),
    IsLQGMeasureOfField P γ γ (translatedCircle hcirc z) μT ∧
    IsLQGMetricOfField P γ ξ γ (translatedPairing hC hcirc z) DT ∧
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (FirstPassS11i.CertificateEvent (κ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2)
          (m (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2) Ostar U V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μT ω) (DT ω) Ostar U V W T Q' Q η M (certScale n) 0)

/-- **Termwise identification at the insertion `0`, from the seed and the model certificate at the root.** -/
theorem rootedTermwise_of_modelCertificate {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (A : Set ℂ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hPhys : RootedModelCertificateStmt P γ ξ hC hcirc c₁ c₂ r₁ r₂ κ m Ostar U V W T Q' Q η M) :
    RootedCertificateTermwiseIdentificationStmt P γ 0 hC hcirc c₁ c₂ r₁ r₂ A E κ m Ostar U V W T Q' Q η M := by
  classical
  set S : Set (ModConstTestPairings (univ : Set ℂ)) := canonRestrict (ball (0 : ℂ) 7) ⁻¹' E with hSdef
  have hS : MeasurableSet S := measurable_canonRestrict _ hE
  have h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
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
    ae_all_iff.2 fun n => ae_iterate_mem_iff_certificate hγ hS h0 n Ω P _ _ μT DT hGT hμT hDT
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

/-- **The reference-null field from the model certificate at the root.** For a whole-plane model, decoders `κ`, `m` on
`B_{r₂}(c₂) ⊇ closedBall c₁ r₁`, and a coding event `E` with common probability `q`, the seed `hEq` and the model
certificate at the root give: for Lebesgue-almost every `z ∈ B_{r₁}(c₁)`, almost surely the Campbell reference
observation at `z` is not in the bad window set of the decoded local certificates at level `q`. -/
theorem href_of_modelCertificate {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {q : ℝ} (hq : CommonProb.{0} γ E q)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hPhys : RootedModelCertificateStmt P γ ξ hC hcirc c₁ c₂ r₁ r₂ κ m Ostar U V W T Q' Q η M) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U V W T Q' Q η M) q := by
  have hT := rootedTermwise_of_modelCertificate hγ hE hEq hG hsub Set.univ κ m hPhys
  have h := FirstPassS11iStep8Href.ae_href_of_termwise
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived birkhoffPointwiseErgodic_derived hG Set.univ hE κ m
    Ostar U V W T Q' Q η M hT
  have hq' : q = (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' E}).toReal :=
    (hq Ω P hC hcirc hG).symm
  rw [hq']
  rw [ae_restrict_iff' measurableSet_ball] at h
  exact h.mono fun z hz hzB => hz hzB (mem_univ z)

/-- **The named field `hHref` of `insertionZeroUnit_of_href` (`S11i/InsertionZeroUnitE.lean`), from the seed and the
model certificate at the root for the ball decoders.** No canonical decoder and no uniqueness of the LQG metric are
used. -/
theorem hHref_of_modelCertificate {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    (hPhys : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ)
      (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          RootedModelCertificateStmt P γ (lqgXi γ) hC' hcirc' (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)
            (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
        (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' → HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q := by
  intro Ω _ P _ q hq hC' hcirc' _ 𝔇 h𝔇 hG _ p hp
  exact href_of_modelCertificate hγ0 hE hEq hq hG (validBall_facts hp).2.1 _ _
    (hPhys Ω P hC' hcirc' 𝔇 h𝔇 hG p hp)

end HarmonicBalls.FirstPassPhase2Step8HrefOfModel
