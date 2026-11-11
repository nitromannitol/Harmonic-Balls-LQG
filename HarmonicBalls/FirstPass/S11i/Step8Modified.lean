import HarmonicBalls.FirstPass.S11ao
import HarmonicBalls.FirstPass.S11ah.Step5Local
import HarmonicBalls.FirstPass.S11ah.Modified
import HarmonicBalls.FirstPass.S11ah.LocalObsHae
import HarmonicBalls.FirstPass.S11ah.LocalObsHaeGood
import HarmonicBalls.FirstPass.S11ah.FiniteLocalKernel
import HarmonicBalls.FirstPass.S11i.Step8LocalFailure
import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11i.Step8Normalized
import HarmonicBalls.FirstPass.S11i.Step8MarkedMem
import HarmonicBalls.FirstPass.S11i.Step8Frequency

/-!
# Modified local decoder and the marked transfer of the failure set (Step 8 chain)

Assembly of the Stage-B pieces. Given the local decoder `mC` (a family of
continuous functions on `ball c₂ r₂ × ball c₂ r₂`, measurable in the observation, with identity (20) of
`LocalMetricReplacementStmt` at `α₀` for the rooted reference observations), and the measure kernel `κ` (measurable):

1. `hae` (the a.s. length property of the decoders `decoderOn (ball c₂ r₂) (mC ℓ)` under `rootedRefLaw`) comes from
   `ae_isLengthMetricOn_rootedRefLaw` with `hGood` from `hGood_of_measurable` (`S11ah/LocalObsHaeGood.lean`), which uses
   only `Measurable mC` and `0 < r₂`.
2. `hDm` (pointwise measurability of the decoder) follows from `Measurable mC`.
3. `hloc` (`CertificateEventLocality`) comes from the containments `hCC` (`certificateEventLocality_of_containments`).
4. The normalized kernel `κ' = discNormalizedKernel κ` is a finite kernel (`isFiniteKernel_discNormalizedKernel`), and
   the a.s. positivity `hκpos` of its normalizing factor follows from the named finiteness `hkappa`.
5. `exists_measurable_localLengthModification` gives a measurable `H` with `rootedRefLaw Hᶜ = 0` and a measurable
   modification `D'` of the decoder with `D' = decoderOn (mC)` on `H` (`S11ao.lean:44`).
6. The modified failure set `failureSet U (localCertSeq κ' D')` is measurable (`Step5Local.lean:120`).
7. `rootedCertTermwise_of_normalized_modified`, `ae_not_mem_failureSet_of_localCert` and
   `ae_marked_local_transfer_landed` transfer the termwise identity to the marked law `μα`.
8. `ae_markedObs_mem_modificationSet` gives marked observations in `H`.

Named inputs: `hT` (the termwise identification, `RootedCertificateTermwiseIdentificationStmt`), `hid` (identity (20) of
`LocalMetricReplacementStmt` at `α₀`, for the given `mC`), `hmC` (the conjunct `Measurable m` of
`LocalMetricReplacementStmt`), `hfr` (frozen rooted continuity), `hkappa` (a.s. finiteness of the mass of the disc under
`κ` at the rooted reference observations), and the frozen Step-8 inputs of the transfer.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Modified

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ah FirstPassS11ai HarmonicBalls.FirstPassS11ahLocalHae HarmonicBalls.FirstPassS11iStep8Frequency
  HarmonicBalls.FirstPassS11iStep8MarkedMem HarmonicBalls.FirstPassS11iStep8Normalized

/-- The Step-8 normalized kernel `ℓ ↦ (1 + κ ℓ (ball c₂ r₂))⁻¹ • κ ℓ|_{ball c₂ r₂}` on the decoder disc (the
normalization used in the proof of `FirstPassS11ahFinite.exists_finite_localMeasureKernel`,
`S11ah/FiniteLocalKernel.lean`, here for a given measurable kernel `κ`). -/
noncomputable def discNormalizedKernel {c₂ : ℂ} {r₂ : ℝ} (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ)
    (hκm : Measurable κ) : Kernel (FirstPassS11ahFinite.LocalObs c₂ r₂) ℂ :=
  ⟨fun ℓ => (1 + κ ℓ (ball c₂ r₂))⁻¹ • (κ ℓ).restrict (ball c₂ r₂), by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact ((measurable_const.add ((Measure.measurable_coe measurableSet_ball).comp hκm)).inv).mul
      ((Measure.measurable_coe (hs.inter measurableSet_ball)).comp hκm)⟩

theorem discNormalizedKernel_apply {c₂ : ℂ} {r₂ : ℝ} (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ)
    (hκm : Measurable κ) (ℓ : FirstPassS11ahFinite.LocalObs c₂ r₂) :
    discNormalizedKernel κ hκm ℓ = (1 + κ ℓ (ball c₂ r₂))⁻¹ • (κ ℓ).restrict (ball c₂ r₂) :=
  rfl

/-- The normalized kernel is a finite kernel: its mass on the whole space is at most `1`. -/
theorem isFiniteKernel_discNormalizedKernel {c₂ : ℂ} {r₂ : ℝ}
    (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ) (hκm : Measurable κ) :
    IsFiniteKernel (discNormalizedKernel κ hκm) := by
  have hbound : ∀ ℓ, discNormalizedKernel κ hκm ℓ univ ≤ 1 := by
    intro ℓ
    rw [discNormalizedKernel_apply, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact FirstPassS11ahFinite.inv_one_add_mul_le_one _
  exact ⟨⟨1, ENNReal.one_lt_top, hbound⟩⟩

/-- If the mass of the disc is finite at `ℓ`, the normalized kernel is a positive multiple of `κ ℓ` on the disc. -/
theorem exists_pos_discNormalizedKernel_restrict {c₂ : ℂ} {r₂ : ℝ}
    (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ) (hκm : Measurable κ)
    (ℓ : FirstPassS11ahFinite.LocalObs c₂ r₂) (hfin : κ ℓ (ball c₂ r₂) ≠ ⊤) :
    ∃ s : ℝ, 0 < s ∧
      (discNormalizedKernel κ hκm ℓ).restrict (ball c₂ r₂) =
        ENNReal.ofReal s • (κ ℓ).restrict (ball c₂ r₂) := by
  have hinv0 : (1 + κ ℓ (ball c₂ r₂))⁻¹ ≠ 0 := by simp [hfin]
  have hinvt : (1 + κ ℓ (ball c₂ r₂))⁻¹ ≠ ⊤ := by simp
  refine ⟨((1 + κ ℓ (ball c₂ r₂))⁻¹).toReal, ENNReal.toReal_pos hinv0 hinvt, ?_⟩
  rw [discNormalizedKernel_apply, Measure.restrict_smul, Measure.restrict_restrict measurableSet_ball,
    Set.inter_self, ENNReal.ofReal_toReal hinvt]

/-- The a.s. positivity `hκpos` of the normalizing factor, from the a.s. finiteness `hkappa` of the disc mass. -/
theorem hκpos_of_discNormalizedKernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ) (hκm : Measurable κ)
    (hkappa : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 (ball c₂ r₂) ≠ ⊤) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ s : ℝ, 0 < s ∧
      (discNormalizedKernel κ hκm (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
        ENNReal.ofReal s • (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) := by
  filter_upwards [hkappa] with z hz
  filter_upwards [hz] with ω hω
  exact exists_pos_discNormalizedKernel_restrict κ hκm _ hω

/-- Pointwise measurability of the decoder `decoderOn (ball c₂ r₂) (mC ℓ)` in the observation `ℓ`, from the measurability
of `mC` (the conjunct `Measurable m` of `LocalMetricReplacementStmt`). -/
theorem measurable_decoderOn_apply {c₂ : ℂ} {r₂ : ℝ}
    {mC : FirstPassS11ahFinite.LocalObs c₂ r₂ → ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ}
    (hmC : Measurable mC) {x y : ℂ} (hx : x ∈ ball c₂ r₂) (hy : y ∈ ball c₂ r₂) :
    Measurable fun ℓ => decoderOn (ball c₂ r₂) (mC ℓ) x y := by
  have hxy : (x, y) ∈ ball c₂ r₂ ×ˢ ball c₂ r₂ := ⟨hx, hy⟩
  have h : (fun ℓ => decoderOn (ball c₂ r₂) (mC ℓ) x y) = fun ℓ => mC ℓ ⟨(x, y), hxy⟩ := by
    funext ℓ
    simp [decoderOn, hxy]
  rw [h]
  exact (ContinuousMap.measurable_eval _).comp hmC

/-- **Marked failure set of the modified decoder.** For a.e. model `ω` and `μα ω`-a.e. marked root `z` in the unit
ball, the marked observation is not in the modified failure set, and the marked observations at roots of the disc lie
in the modification set `H`. -/
theorem ae_marked_modified_failureSet {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hR₂ : 0 < r₂) (h12 : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h21 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1) (hc0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (hsub : ball (0 : ℂ) 1 ⊆ ball c₁ r₁)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{0})
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (hB : BirkhoffPointwiseErgodic.{0})
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ) (hκm : Measurable κ)
    (mC : FirstPassS11ahFinite.LocalObs c₂ r₂ → ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hmC : Measurable mC)
    (ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (hL : IsLQGMetric γ ξ 𝔇)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hid : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (mC (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (weylPhysicalE (𝔇 (hC ω)) ξ
            (fun w => -α₀ * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
            (ball c₂ r₂) p.1.1 p.1.2)
    (hkappa : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 (ball c₂ r₂) ≠ ⊤)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hUsub : U ⊆ closedBall 0 7)
    (hT : FirstPassS11ai.RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂
      (ball (0 : ℂ) 1) F κ (fun ℓ => decoderOn (ball c₂ r₂) (mC ℓ)) Ostar U V W T Q' Q η M)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η)
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0) :
    ∃ (H : Set (FirstPassS11ahFinite.LocalObs c₂ r₂))
      (D' : FirstPassS11ahFinite.LocalObs c₂ r₂ → ℂ → ℂ → ℝ),
      MeasurableSet H ∧ rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC Hᶜ = 0 ∧
      (∀ ℓ ∈ H, D' ℓ = decoderOn (ball c₂ r₂) (mC ℓ)) ∧
      (∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂, Measurable fun ℓ => D' ℓ x y) ∧
      (∀ ℓ, IsLengthMetricOn (ball c₂ r₂) (D' ℓ)) ∧
      (∀ᵐ ω ∂P,
        (∀ᵐ z ∂(μα ω), z ∈ ball (0 : ℂ) 1 →
          campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉
            failureSet U (localCertSeq (fun ℓ => discNormalizedKernel κ hκm ℓ) D' Ostar U V W T Q' Q η M)
              (step8Frequency P γ hC F)) ∧
        (∀ᵐ z ∂(μα ω).restrict (ball c₁ r₁), (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H)) := by
  have : IsFiniteKernel (discNormalizedKernel κ hκm) := isFiniteKernel_discNormalizedKernel κ hκm
  have hκpos := hκpos_of_discNormalizedKernel κ hκm hkappa
  have hae : ∀ᵐ ℓ ∂(rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC),
      IsLengthMetricOn (ball c₂ r₂) (decoderOn (ball c₂ r₂) (mC ℓ)) :=
    ae_isLengthMetricOn_rootedRefLaw hG hL hfr hγ0 hγ2 hα h12 hc0 mC hid
      (HarmonicBalls.FirstPassS11ahLocalObsHaeGood.hGood_of_measurable hR₂ hmC)
  have hDm : ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      Measurable fun ℓ => decoderOn (ball c₂ r₂) (mC ℓ) x y :=
    fun x hx y hy => measurable_decoderOn_apply hmC hx hy
  obtain ⟨H, hH, hPH, D', hD'm, hD'l, hagree, -⟩ :=
    FirstPassS11ao.exists_measurable_localLengthModification (P := rootedRefLaw P γ α₀ c₁ c₂ r₁ r₂ hC)
      (convex_ball c₂ r₂) isOpen_ball hDm hae
  have hmeasF := FirstPassS11ah.measurableSet_failureSet_disc hR₂ (discNormalizedKernel κ hκm) hD'm hD'l
    (certificateEventLocality_of_containments (U := U) (M := M) hCC) hOstar h0 hsph hU hη hU (step8Frequency P γ hC F)
  have hrefH := ae_refObs_mem_of_rootedRefLaw_compl_null hG hH hPH
  have hT' := rootedCertTermwise_of_normalized_modified P γ α₀ hC hcirc c₁ c₂ r₁ r₂ (ball (0 : ℂ) 1) F
    κ (fun ℓ => discNormalizedKernel κ hκm ℓ) (fun ℓ => decoderOn (ball c₂ r₂) (mC ℓ)) D' Ostar U V W T Q' Q η M
    hCC hUsub hT hκpos H hrefH (fun ℓ hℓ => (hagree ℓ hℓ).2)
  have href := FirstPassS11iStep8LocalFailure.ae_not_mem_failureSet_of_localCert hCM hB hG hsub hF
    (fun ℓ => discNormalizedKernel κ hκm ℓ) D' Ostar U V W T Q' Q η M hT'
  have hmark := FirstPassS11iStep8Corrected.ae_marked_local_transfer_landed hWeyl γ α₀ hγ0 hγ2 hα
    (ball c₂ r₂) μ0 μα hA10 hG hμ0 hμα hNon0 hNonα
    (failureSet U (localCertSeq (fun ℓ => discNormalizedKernel κ hκm ℓ) D' Ostar U V W T Q' Q η M)
      (step8Frequency P γ hC F))
    hmeasF href
  have hmarkH := ae_markedObs_mem_modificationSet hWeyl γ α₀ hγ0 hγ2 hα h12 h21 μ0 μα hA10 hG hμ0 hμα
    hNon0 hNonα hH hrefH
  refine ⟨H, D', hH, hPH, fun ℓ hℓ => (hagree ℓ hℓ).2, hD'm, hD'l, ?_⟩
  filter_upwards [hmark, hmarkH] with ω h1 h2
  exact ⟨h1, h2⟩

end HarmonicBalls.FirstPassS11iStep8Modified

