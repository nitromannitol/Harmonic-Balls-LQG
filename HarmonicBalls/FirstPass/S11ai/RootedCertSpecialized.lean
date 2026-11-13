import HarmonicBalls.FirstPass.S11ai.RootedIdentification
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11ah.LocalCert

/-!
# Specialized rooted certificate identity

`ae_rootedId_of_termwise` (RootedIdentification.lean:62) takes the termwise identity `hT` for an arbitrary sequence `c` and an
arbitrary event `F`. This file states it for the actual Step 8
certificate: `c n (z, ℓ) = localCert (ball c₂ r₂) κ m … n ℓ z`, the decoded local certificate of the Campbell reference
observation at the root `z` (sequence (J); the field `sequence_eq` of
`CertificateIdentification`, `FirstPass/S11i/Identification.lean:33`). The coding event `F` stays a parameter: it is the
scale-one event of the Step 8 identification. The eventual covariance lemma (`RootedCertificateEventualCovarianceStmt`,
FirstPass/S11at.lean) is not yet in the repository; the statement below is the hypothesis until it lands. No new input.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c
open FirstPassS11ah

/-- The Step 8 certificate sequence on Campbell reference observations: `c n (z, ℓ)` is the decoded local certificate of
`ℓ` (restriction to `ball c₂ r₂`) at radius `2⁻ⁿ` about `z`, with local decoders `κ` (measure) and `m` (metric). -/
noncomputable def localCertSeq {c₂ : ℂ} {r₂ : ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) :
    ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ :=
  fun n p => localCert (ball c₂ r₂) κ m Ostar U V W T Q' Q η M n p.2 p.1

/-- **Specialized termwise certificate identity (Lemma 11.13, Step 8, "legitimate local transfer", corrected draft lines
3873-3880).** For Lebesgue-a.e. root `z ∈ A` in `ball c₁ r₁`, every admissible shift `(b, u)` (`0 < b`, `2b < ‖z‖`, `2b < 1`,
`u` smooth with compact support, zero circle average, `u = -α₀ log‖z + ·‖` on `ball 0 b`), almost surely the decoded local
certificate of the Campbell reference observation at `z` is eventually equal to the coding event `F` evaluated at the
dilated, shifted canonical field. Source: corrected draft lines 3873-3880; ingredients the certificate definitions, local
decoder identification, Cameron-Martin, translation and dyadic covariance. -/
def RootedCertificateTermwiseIdentificationStmt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Prop :=
  ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), 0 < b → 2 * b < ‖z‖ → 2 * b < 1 →
    ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → Real.circleAverage u 0 1 = 0 →
    (∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖) →
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      localCertSeq κ m Ostar U V W T Q' Q η M n (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) =
        (ballRestrictPairing 7 ⁻¹' F).indicator (fun _ => (1 : ℝ))
          (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)))

/-- **Specialized termwise identity `hT` with the decoded rooted pair.** The rooted pair is the decoded
pair `(rootedMeasDec, rootedMetricDec)` of `RootedInstance.lean`, so the fitting clause holds by reflexivity and is not an
input. The sequence is the Step 8 local certificate `localCertSeq` (`hSeq` holds by definition). Named input: `hCov`,
`RootedCertificateEventualCovarianceStmt` for the decoded pair (pending). `hFdef` says
that the coding event `F` is the scale-one certificate event (defining identity of `F`), so `hG` holds pointwise. The proof is
`ae_termwise_of_identification`. -/
theorem rootedCertTermwise_of_decoded {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (A : Set ℂ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
      (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F) :
    RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ m Ostar U V W T Q' Q η M := by
  have hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) :=
    Filter.Eventually.of_forall fun z _ b u _ =>
      Filter.Eventually.of_forall fun ω n => hFdef _
  exact ae_termwise_of_identification (F := F) hsub A Ostar U V W T Q' Q η M κ m
    (localCertSeq κ m Ostar U V W T Q' Q η M) (fun _ _ _ => rfl) Dμ Dd hCov hG

/-- The specialized termwise identity gives the rooted decoder identification `hId` of `ae_window_limit_at_root`, by the
generic assembly `ae_rootedId_of_termwise` with `c = localCertSeq κ m …`. -/
theorem ae_rootedId_of_localCert {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hT : RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ m Ostar U V W T Q' Q η M) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∃ (b : ℝ) (u : ℂ → ℝ), 0 < b ∧
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧ ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
        ReferenceNullS11i.refWindowAverage (localCertSeq κ m Ostar U V W T Q' Q η M)
            N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)
          = windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (addFunPairing (translatedPairing hC hcirc z ω) u) N :=
  ae_rootedId_of_termwise A (localCertSeq κ m Ostar U V W T Q' Q η M) hT

end FirstPassS11ai

