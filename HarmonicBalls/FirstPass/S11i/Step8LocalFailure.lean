import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11ai
import HarmonicBalls.FirstPass.S11ai.RootedCertSpecialized
import HarmonicBalls.FirstPass.S11ah.FailureSet

/-!
# Local failure set of the Step 8 window frequency, and the reference hypothesis `href`

The reference
observation `campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z` avoids the local failure set, obtained from
`ae_window_limit_at_root` and `ae_rootedId_of_localCert`, with the specialized termwise identity `hT`.

What is proved here (no new hypothesis):
* `ae_not_mem_failureSet_of_localCert`: for a.e. root `z` in the unit ball, almost surely the reference observation is not in
  the local failure set `failureSet U (localCertSeq κ m ...) q` with `q = P{alphaCanon ∈ F}.toReal`. The value of `q` is the
  limit fixed by `ae_window_limit_at_root`, not a free parameter (this is the G4 fidelity point of `UnitBallFrequencyModelsStmt`).
* `ae_marked_local_transfer_localFailure`: the corrected marked transfer (`ae_marked_local_transfer_landed`) applied to that
  failure set. Its only input beyond the frozen/Proposed inputs is `hBad`, the measurability of the local failure set; this is
  the open measurability gap `hmeas` (`localCertSeq` measurable in the observation), see `Step8PerBall.lean:52`.

Literature inputs used as explicit hypotheses only: `CameronMartinGFFMutualAbsCont` (`hCM`), `BirkhoffPointwiseErgodic` (`hB`),
the frozen DMS identity `DMSLemmaA10WholePlaneMarked` (`hA10`), `LocalLQGInsertionWeylOffOrigin` (`hWeyl`), and the termwise
identity `RootedCertificateTermwiseIdentificationStmt` (`hT`).
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8LocalFailure

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c

/-- **Reference hypothesis `href` from the rooted route (Step 8).** For `volume`-a.e. root `z` in the unit ball,
almost surely the Campbell reference observation at `z` is not in the local failure set of the window averages of the
local certificate sequence, whose limit is `q = P{alphaCanon ∈ F}.toReal` (`ae_window_limit_at_root`). The proof: the termwise
identity `hT` gives the eventual identity of window averages for a.e. root (`ae_rootedId_of_localCert`), then the window
limit holds almost surely, and a convergent sequence is not in the failure set. -/
theorem ae_not_mem_failureSet_of_localCert {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : ball (0 : ℂ) 1 ⊆ ball c₁ r₁)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hT : FirstPassS11ai.RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂
      (ball (0 : ℂ) 1) F κ m Ostar U V W T Q' Q η M) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        FirstPassS11ah.failureSet U (FirstPassS11ai.localCertSeq κ m Ostar U V W T Q' Q η M)
          (P {ω' | alphaCanon γ hC ω' ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have h1 := FirstPassS11ai.ae_rootedId_of_localCert (ball (0 : ℂ) 1) κ m Ostar U V W T Q' Q η M hT
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp h1] with z hz hz01
  have hid := hz (hsub hz01) hz01
  filter_upwards [FirstPassS11ai.ae_window_limit_at_root hCM hB hh
    (FirstPassS11ai.localCertSeq κ m Ostar U V W T Q' Q η M) z hF hid] with ω hω
  intro hmem
  exact ((FirstPassS11ah.mem_failureSet_iff _).mp hmem).2 hω

/-- **Corrected marked transfer with the local failure set (Step 8).** Applies
`ae_marked_local_transfer_landed` to the local failure set of the window averages of `localCertSeq`, with the reference
hypothesis `href` discharged by `ae_not_mem_failureSet_of_localCert`. The remaining named input is `hBad`: measurability of
the local failure set. -/
theorem ae_marked_local_transfer_localFailure {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : ball (0 : ℂ) 1 ⊆ ball c₁ r₁)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hT : FirstPassS11ai.RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂
      (ball (0 : ℂ) 1) F κ m Ostar U V W T Q' Q η M)
    (hBad : MeasurableSet (FirstPassS11ah.failureSet U (FirstPassS11ai.localCertSeq κ m Ostar U V W T Q' Q η M)
      (P {ω' | alphaCanon γ hC ω' ∈ ballRestrictPairing 7 ⁻¹' F}).toReal)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball (0 : ℂ) 1 →
      campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉
        FirstPassS11ah.failureSet U (FirstPassS11ai.localCertSeq κ m Ostar U V W T Q' Q η M)
          (P {ω' | alphaCanon γ hC ω' ∈ ballRestrictPairing 7 ⁻¹' F}).toReal :=
  FirstPassS11iStep8Corrected.ae_marked_local_transfer_landed hWeyl γ α₀ hγ0 hγ2 hα (ball c₂ r₂) μ0 μα hA10 hGFF
    hμ0 hμα hNon0 hNonα _ hBad
    (ae_not_mem_failureSet_of_localCert hCM hB hGFF hsub hF κ m Ostar U V W T Q' Q η M hT)

end HarmonicBalls.FirstPassS11iStep8LocalFailure

