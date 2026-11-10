import HarmonicBalls.FirstPass.S11ao
import HarmonicBalls.FirstPass.S11ah.Step5Local
import HarmonicBalls.FirstPass.S11i.Step8LocalFailure
import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11i.Step8Normalized
import HarmonicBalls.FirstPass.S11i.Step8MarkedMem
import HarmonicBalls.FirstPass.S11i.Step8Frequency

/-!
# Modified local decoder and the marked transfer of the failure set (Step 8 chain, owner n3)

Assembly of the Stage-B pieces for fp-S11i-11-13h. Given the rooted decoder `m` (raw) with an a.s. local length property
under the rooted-reference law `Pm = rootedRefLaw`, and the normalized kernel `κ'`:

1. `exists_measurable_localLengthModification` gives a measurable `H` with `Pm Hᶜ = 0` and a measurable modification
   `D'` with `D' = m` on `H` (`S11ao.lean:44`).
2. The modified failure set `failureSet U (localCertSeq κ' D')` is measurable (`Step5Local.lean:120`).
3. `rootedCertTermwise_of_normalized_modified` gives the termwise identity for `(κ', D')`.
4. `ae_not_mem_failureSet_of_localCert` gives the reference-side null statement for `(κ', D')`.
5. `ae_marked_local_transfer_landed` transfers it to the marked law `μα`.
6. `ae_markedObs_mem_modificationSet` gives marked observations in `H`.

Named inputs: `hae` (the a.s. length property under `Pm`, from B1 via `ae_isLengthMetricOn_rootedRefLaw`, whose
`hGood` is still open), `hloc` (`CertificateEventLocality`), and the frozen Step-8 inputs of the transfer.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Modified

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ah FirstPassS11ai HarmonicBalls.FirstPassS11ahLocalHae HarmonicBalls.FirstPassS11iStep8Frequency
  HarmonicBalls.FirstPassS11iStep8MarkedMem HarmonicBalls.FirstPassS11iStep8Normalized

/-- **Marked failure set of the modified decoder.** For a.e. model `ω` and `μα ω`-a.e. marked root `z` in the unit
ball, the marked observation is not in the modified failure set, and the marked observations at roots of the disc lie
in the modification set `H`. -/
theorem ae_marked_modified_failureSet {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hR₂ : 0 < r₂) (h12 : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h21 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1) (hsub : ball (0 : ℂ) 1 ⊆ ball c₁ r₁)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{0})
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (hB : BirkhoffPointwiseErgodic.{0})
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ' : Kernel (FirstPassS11ahFinite.LocalObs c₂ r₂) ℂ) [IsFiniteKernel κ']
    (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ)
    (m : FirstPassS11ahFinite.LocalObs c₂ r₂ → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hUsub : U ⊆ closedBall 0 7)
    (hT : FirstPassS11ai.RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂
      (ball (0 : ℂ) 1) F κ m Ostar U V W T Q' Q η M)
    (hκpos : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ s : ℝ, 0 < s ∧
      (κ' (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
        ENNReal.ofReal s • (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂))
    (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η)
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    (hae : ∀ᵐ ℓ ∂(rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC), IsLengthMetricOn (ball c₂ r₂) (m ℓ))
    (hDm : ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      Measurable fun ℓ : FirstPassS11ahFinite.LocalObs c₂ r₂ => m ℓ x y) :
    ∃ (H : Set (FirstPassS11ahFinite.LocalObs c₂ r₂))
      (D' : FirstPassS11ahFinite.LocalObs c₂ r₂ → ℂ → ℂ → ℝ),
      MeasurableSet H ∧ rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC Hᶜ = 0 ∧
      (∀ ℓ ∈ H, D' ℓ = m ℓ) ∧
      (∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂, Measurable fun ℓ => D' ℓ x y) ∧
      (∀ ℓ, IsLengthMetricOn (ball c₂ r₂) (D' ℓ)) ∧
      (∀ᵐ ω ∂P,
        (∀ᵐ z ∂(μα ω), z ∈ ball (0 : ℂ) 1 →
          campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉
            failureSet U (localCertSeq (fun ℓ => κ' ℓ) D' Ostar U V W T Q' Q η M)
              (step8Frequency P γ hC F)) ∧
        (∀ᵐ z ∂(μα ω).restrict (ball c₁ r₁), (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H)) := by
  obtain ⟨H, hH, hPH, D', hD'm, hD'l, hagree, -⟩ :=
    FirstPassS11ao.exists_measurable_localLengthModification (P := rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC)
      (convex_ball c₂ r₂) isOpen_ball hDm hae
  have hmeasF := FirstPassS11ah.measurableSet_failureSet_disc hR₂ κ' hD'm hD'l hloc hOstar h0 hsph hU hη hU
    (step8Frequency P γ hC F)
  have hrefH := ae_refObs_mem_of_rootedRefLaw_compl_null hG hH hPH
  have hT' := rootedCertTermwise_of_normalized_modified P γ α₀ hC hcirc c₁ c₂ r₁ r₂ (ball (0 : ℂ) 1) F
    κ (fun ℓ => κ' ℓ) m D' Ostar U V W T Q' Q η M hCC hUsub hT hκpos H hrefH
    (fun ℓ hℓ => (hagree ℓ hℓ).2)
  have href := FirstPassS11iStep8LocalFailure.ae_not_mem_failureSet_of_localCert hCM hB hG hsub hF
    (fun ℓ => κ' ℓ) D' Ostar U V W T Q' Q η M hT'
  have hmark := FirstPassS11iStep8Corrected.ae_marked_local_transfer_landed hWeyl γ α₀ hγ0 hγ2 hα
    (ball c₂ r₂) μ0 μα hA10 hG hμ0 hμα hNon0 hNonα
    (failureSet U (localCertSeq (fun ℓ => κ' ℓ) D' Ostar U V W T Q' Q η M) (step8Frequency P γ hC F))
    hmeasF href
  have hmarkH := ae_markedObs_mem_modificationSet hWeyl γ α₀ hγ0 hγ2 hα h12 h21 μ0 μα hA10 hG hμ0 hμα
    hNon0 hNonα hH hrefH
  refine ⟨H, D', hH, hPH, fun ℓ hℓ => (hagree ℓ hℓ).2, hD'm, hD'l, ?_⟩
  filter_upwards [hmark, hmarkH] with ω h1 h2
  exact ⟨h1, h2⟩

end HarmonicBalls.FirstPassS11iStep8Modified

#print axioms HarmonicBalls.FirstPassS11iStep8Modified.ae_marked_modified_failureSet
