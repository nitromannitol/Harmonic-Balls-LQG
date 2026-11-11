import Mathlib
import HarmonicBalls.FirstPass.S11ai
import HarmonicBalls.FirstPass.S11ai.RootedCertSpecialized
import HarmonicBalls.FirstPass.S11at
import HarmonicBalls.FirstPass.S11i.Step8Frequency
import HarmonicBalls.FirstPass.S11ah.LQGDecoder

/-!
# Step 8: the reference window limit at a.e. root (input `href`)

This file produces the input `href` of `ae_unitScale_of_ball` (`Step8Exhaustion.lean`) from the termwise identity
`RootedCertificateTermwiseIdentificationStmt` (the Step 8 local certificate sequence `localCertSeq`).
For `volume`-a.e. root `z` of a ball `ball c₁ r₁ ⊆ ball c₂ r₂`, the reference observation of `z` has window average
tending to `q = P{α ∈ F}`; hence it is not in the bad window set of level `q`.

Chain: termwise identity `hT` → `ae_rootedId_of_localCert` (rooted identity for a.e. root) →
`ae_window_limit_at_root` (window limit `P{α ∈ F}` at the root) → not in `refBadWindowSet`.
The covariance input `hCov` enters through `rootedCertTermwise_of_decoded` (with `hFdef`); the extra hypotheses of
`FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded` are not discharged here.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Href

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c
open FirstPassS11ai FirstPassS11at FirstPassS11i

/-- **`href` from the termwise identity.** For `volume`-a.e. root `z` in `A` (restricted to `ball c₁ r₁`), almost surely the
reference observation of `z` is not in the bad window set of level `q = P{α ∈ F}` of the local certificate sequence. -/
theorem ae_href_of_termwise {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ) {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hT : RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ m Ostar U V W T Q' Q η M) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  filter_upwards [ae_rootedId_of_localCert A κ m Ostar U V W T Q' Q η M hT] with z hz hzA
  obtain ⟨b, u, hb, hu, hcomp, hu0, hid⟩ := hz hzA
  filter_upwards [ae_window_limit_at_root hCM hB hh (localCertSeq κ m Ostar U V W T Q' Q η M) z hF
    ⟨b, u, hb, hu, hcomp, hu0, hid⟩] with ω hω
  exact fun hbad => hbad hω

/-- **`href` on a ball from the covariance input.** For the decoded rooted pair, the covariance input `hCov`
(`RootedCertificateEventualCovarianceStmt` with `Adm = AdmissibleRootShift α₀`, `rR = rootRadius`) and the identification
`hFdef` of the scale-one certificate event with `F` give `href` for `volume`-a.e. root `z ∈ ball c₁ r₁`, where
`closedBall c₁ r₁ ⊆ ball c₂ r₂`. The root set is `A = univ`. -/
theorem ae_href_of_covariance {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have hT := rootedCertTermwise_of_decoded hsub Set.univ F κ m Ostar U V W T Q' Q η M Dμ Dd hCov hFdef
  have h := ae_href_of_termwise hCM hB hh Set.univ hF κ m Ostar U V W T Q' Q η M hT
  rw [ae_restrict_iff' measurableSet_ball] at h
  exact h.mono fun z hz hzB => hz hzB (mem_univ z)

/-- The window metric of a continuous decoder is the decoder function `decoderOn` of the disc. -/
theorem windowMetric_eq_decoderOn {c : ℂ} {r : ℝ}
    (mC : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
      C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ))
    (φ : {φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) :
    FirstPassS11at.windowMetric (ball c r) mC φ = FirstPassS11ah.decoderOn (ball c r) (mC φ) := by
  funext x y
  unfold FirstPassS11at.windowMetric FirstPassS11ah.decoderOn
  by_cases h : (x, y) ∈ ball c r ×ˢ ball c r <;> simp [h]

/-- **Bridge from the decoded covariance to the reference failure set.** The covariance input is stated for the decoded
pair of `FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent` (`decodedRootMeasure κ`,
`decodedRootMetric (windowMetric (ball c₂ r₂) mC)`) with the continuous decoder `mC`; the certificate uses the decoder
function `decoderOn (ball c₂ r₂) (mC ·)`, which is the same function (`windowMetric_eq_decoderOn`). -/
theorem ae_href_of_decoded_covariance {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mC : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)), ℝ))
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC)
      (FirstPassS11at.decodedRootMetric (FirstPassS11at.windowMetric (ball c₂ r₂) mC) γ α₀ hC) Dμ Dd) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq κ (fun ℓ => FirstPassS11ah.decoderOn (ball c₂ r₂) (mC ℓ)) Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have e : FirstPassS11at.decodedRootMetric (FirstPassS11at.windowMetric (ball c₂ r₂) mC) γ α₀ hC =
      FirstPassS11at.decodedRootMetric (fun ℓ => FirstPassS11ah.decoderOn (ball c₂ r₂) (mC ℓ)) γ α₀ hC := by
    funext z ω
    simp only [FirstPassS11at.decodedRootMetric, windowMetric_eq_decoderOn]
  rw [e] at hCov
  exact ae_href_of_covariance hCM hB hh hsub hF κ (fun ℓ => FirstPassS11ah.decoderOn (ball c₂ r₂) (mC ℓ)) Ostar U V W T Q' Q η M
    Dμ Dd hFdef hCov

/-- **The Step-8 frequency is the certificate frequency.** Under `hFdef`, `q_F = step8Frequency P γ hC F` is the
probability of the certificate event of the canonical model at insertion `γ` -/
theorem step8Frequency_eq_certificateFrequency {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F) :
    HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency P γ hC F =
      (P {ω | FirstPassS11i.CertificateEvent (Dμ (alphaCanon γ hC ω)) (Dd (alphaCanon γ hC ω))
        Ostar U V W T Q' Q η M 1 0}).toReal := by
  unfold HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency
  congr 2
  ext ω
  exact (hFdef (alphaCanon γ hC ω)).symm

end HarmonicBalls.FirstPassS11iStep8Href

