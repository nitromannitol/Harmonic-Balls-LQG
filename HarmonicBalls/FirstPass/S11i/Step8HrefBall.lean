import HarmonicBalls.FirstPass.S11i.Step8Modified
import HarmonicBalls.FirstPass.S11i.Step8Href
import HarmonicBalls.FirstPass.S11i.Step8Normalized
import HarmonicBalls.FirstPass.S11i.Step8MarkedMem
import HarmonicBalls.FirstPass.S11i.Step8Frequency

/-!
# `href` on a ball for the normalized pair (Step 8, fp-S11i-11-13k, owner n3)

Chat 238 (`notes/fp-gaps/CHATGPT-238-hb-11-13-n4-per-ball-PRO.md`, section 2 and handoff steps 7-8): the reference
hypothesis `href` of the per-ball Step 8 route, for the normalized finite kernel `κ = discNormalizedKernel κ₀` and a
modified decoder `m`, at the reference observations `campbellReferenceObs γ 0`. The chain is

* `rootedCertTermwise_of_decoded` (raw termwise identity `hT₀` for `(κ₀, m₀)` from the rooted covariance `hCov`
  and the identification `hFdef`);
* `rootedCertTermwise_of_normalized_modified` (transfer to `(κ, m)`, with the a.s. positivity `hκpos` of the
  normalizing factor and `m = m₀` on the observation set `H`);
* `ae_href_of_termwise` (`ae_rootedId_of_localCert` plus `ae_window_limit_at_root` plus the failure set);
* the limit is `P{α_γ ∈ F}`, which is the canonical unit-scale frequency `qF` (model independence:
  `canonical_frequency_eq_of_models`, a corollary of `step8Frequency_eq_of_isWholePlaneGFF`).

Named inputs: the rooted covariance `hCov` (the output of n1's `rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent`,
`S11at.lean:1070`, for the raw pair `(κ₀, m₀)`), the identification `hFdef`, the frozen containments `hCC`, and the a.s.
finiteness `hkappa` of the raw kernel on the disc (`Step8Modified.lean`, `hkappa`). Nothing about `m` beyond
`m = m₀` on `H` is used. The decoder disc is `ball c₂ r₂`; the roots are in `ball c₁ r₁`, and `closedBall c₁ r₁ ⊆ ball c₂ r₂`.
The universe is `Type u`: `rootedRefLaw` (`S11ah/LocalObsHae.lean:38`) and `ae_href_of_termwise` (`S11i/Step8Href.lean:33`)
are stated on `Ω : Type u`, and the frozen input `CameronMartinGFFMutualAbsCont` is taken at the same universe `u`.
-/

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal

universe u

namespace HarmonicBalls.FirstPassS11iStep8HrefBall

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ah FirstPassS11ai FirstPassS11at FirstPassS11i
  HarmonicBalls.FirstPassS11ahLocalHae HarmonicBalls.FirstPassS11iStep8Href
  HarmonicBalls.FirstPassS11iStep8Normalized HarmonicBalls.FirstPassS11iStep8Modified

/-- **`href` of the normalized modified pair on a ball (chat 238, section 2).** Let `κ₀` be a measurable raw kernel on the
decoder disc `ball c₂ r₂` with rooted covariance `hCov` for `(κ₀, m₀)`, and let `κ = discNormalizedKernel κ₀` be its
normalized finite kernel, with `m` a decoder agreeing with `m₀` on the observation set `H` of full rooted reference law
(`hPH`). Then for a.e. root `z` in the root disc `ball c₁ r₁`, almost surely the reference observation of `z` at insertion `0`
avoids the bad window set of `localCertSeq κ m` at the canonical unit-scale frequency `P{α_γ ∈ F}` (`qF`). -/
theorem href_discNormalized_of_covariance {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (κ₀ : FirstPassS11ahFinite.LocalObs c₂ r₂ → Measure ℂ) (hκ₀m : Measurable κ₀)
    (m₀ : FirstPassS11ahFinite.LocalObs c₂ r₂ → ℂ → ℂ → ℝ)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ (ball c₁ r₁)
      Ostar U V W T Q' Q η M (AdmissibleRootShift 0) rootRadius
      (FirstPassS11at.decodedRootMeasure κ₀ γ 0 hC) (FirstPassS11at.decodedRootMetric m₀ γ 0 hC) Dμ Dd)
    (m : FirstPassS11ahFinite.LocalObs c₂ r₂ → ℂ → ℂ → ℝ)
    (H : Set (FirstPassS11ahFinite.LocalObs c₂ r₂)) (hH : MeasurableSet H)
    (hPH : rootedRefLaw P γ 0 c₁ c₂ r₁ r₂ hC Hᶜ = 0)
    (hagree : ∀ l ∈ H, m l = m₀ l)
    (hkappa : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      κ₀ (campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z).2 (ball c₂ r₂) ≠ ⊤) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq (fun ℓ => discNormalizedKernel κ₀ hκ₀m ℓ) m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have hκpos := hκpos_of_discNormalizedKernel κ₀ hκ₀m hkappa
  have hT₀ := rootedCertTermwise_of_decoded hsub (ball c₁ r₁) F κ₀ m₀ Ostar U V W T Q' Q η M Dμ Dd hCov hFdef
  have hrefH := HarmonicBalls.FirstPassS11iStep8MarkedMem.ae_refObs_mem_of_rootedRefLaw_compl_null hG hH hPH
  have hT := rootedCertTermwise_of_normalized_modified P γ 0 hC hcirc c₁ c₂ r₁ r₂ (ball c₁ r₁) F κ₀
    (fun ℓ => discNormalizedKernel κ₀ hκ₀m ℓ) m₀ m Ostar U V W T Q' Q η M hCC hU hT₀ hκpos H hrefH hagree
  have h := ae_href_of_termwise hCM hB hG (ball c₁ r₁) hF (fun ℓ => discNormalizedKernel κ₀ hκ₀m ℓ) m
    Ostar U V W T Q' Q η M hT
  rw [ae_restrict_iff' measurableSet_ball] at h
  exact h.mono fun z hz hzB => hz hzB hzB

/-- **The canonical unit-scale frequency is model independent.** The value `qF = P{α_γ ∈ F}` of
`href_discNormalized_of_covariance` is the same for every whole-plane model (`step8Frequency_eq_of_isWholePlaneGFF`),
so the limit of the href statement can be fixed once for all models. -/
theorem canonical_frequency_eq_of_models {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P hC' hcirc')
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F) :
    (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal =
      (P {ω | alphaCanon γ hC' ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal :=
  FirstPassS11iStep8Frequency.step8Frequency_eq_of_isWholePlaneGFF hh hh' γ hF

/-- **`href` in the doubled-disc instance (n4, `S11i/HzoomUnitBall.lean`, field `Step8UnitBallInputs.href`).** The roots
lie in `ball c r` and the decoders live on the doubled disc `ball c (2 * r)`; n4 takes `c = ballCen p` and `r = ballRad p`
for a valid ball `p` (`ValidBall p` gives `0 < ballRad p`). The inclusion `closedBall c r ⊆ ball c (2 * r)` is
`closedBall_subset_ball` with `r < 2 * r`. This is `href_discNormalized_of_covariance` specialised to
`c₁ = c₂ = c`, `r₁ = r`, `r₂ = 2 * r`; the hypotheses are the same, and `hkappa` stays a named binder (chat 243 Q2). -/
theorem href_discNormalized_doubledDisc {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (κ₀ : FirstPassS11ahFinite.LocalObs c (2 * r) → Measure ℂ) (hκ₀m : Measurable κ₀)
    (m₀ : FirstPassS11ahFinite.LocalObs c (2 * r) → ℂ → ℂ → ℝ)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c c r (2 * r) (ball c r)
      Ostar U V W T Q' Q η M (AdmissibleRootShift 0) rootRadius
      (FirstPassS11at.decodedRootMeasure κ₀ γ 0 hC) (FirstPassS11at.decodedRootMetric m₀ γ 0 hC) Dμ Dd)
    (m : FirstPassS11ahFinite.LocalObs c (2 * r) → ℂ → ℂ → ℝ)
    (H : Set (FirstPassS11ahFinite.LocalObs c (2 * r))) (hH : MeasurableSet H)
    (hPH : rootedRefLaw P γ 0 c c r (2 * r) hC Hᶜ = 0)
    (hagree : ∀ l ∈ H, m l = m₀ l)
    (hkappa : ∀ᵐ z ∂(volume.restrict (ball c r)), ∀ᵐ ω ∂P,
      κ₀ (campbellReferenceObs γ 0 (ball c (2 * r)) (hC ω) z).2 (ball c (2 * r)) ≠ ⊤) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c r → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball c (2 * r)) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq (fun ℓ => discNormalizedKernel κ₀ hκ₀m ℓ) m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have hsub : closedBall c r ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  exact href_discNormalized_of_covariance hCM hB hG hsub hF hCC hU Dμ Dd hFdef κ₀ hκ₀m m₀ hCov m H hH hPH hagree hkappa

/-- **`href` in the doubled-disc instance with the finite decoder kernel (chat 243 Q2, fp-S11i-11-13m).** This is
`href_discNormalized_doubledDisc` at the finite kernel `κF` of `FirstPassS11ahFinite.exists_finite_localMeasureKernel`
(`κF : Kernel (LocalObs c (2 * r)) ℂ`, `[IsFiniteKernel κF]`), with the binder `hkappa` discharged: for every observation
code `ℓ` and every set `s`, `κF ℓ s ≤ κF.bound < ⊤` (`ProbabilityTheory.Kernel.measure_le_bound`,
`ProbabilityTheory.Kernel.bound_lt_top`), so no rooted-measure existence is needed. The second normalization is
`discNormalizedKernel` as in the doubled-disc instance. Hypotheses are otherwise those of `href_discNormalized_doubledDisc`. -/
theorem href_discNormalized_doubledDisc_finiteKernel {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (κF : Kernel (FirstPassS11ahFinite.LocalObs c (2 * r)) ℂ) [IsFiniteKernel κF]
    (m₀ : FirstPassS11ahFinite.LocalObs c (2 * r) → ℂ → ℂ → ℝ)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c c r (2 * r) (ball c r)
      Ostar U V W T Q' Q η M (AdmissibleRootShift 0) rootRadius
      (FirstPassS11at.decodedRootMeasure (fun ℓ => κF ℓ) γ 0 hC) (FirstPassS11at.decodedRootMetric m₀ γ 0 hC) Dμ Dd)
    (m : FirstPassS11ahFinite.LocalObs c (2 * r) → ℂ → ℂ → ℝ)
    (H : Set (FirstPassS11ahFinite.LocalObs c (2 * r))) (hH : MeasurableSet H)
    (hPH : rootedRefLaw P γ 0 c c r (2 * r) hC Hᶜ = 0)
    (hagree : ∀ l ∈ H, m l = m₀ l) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c r → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball c (2 * r)) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq (fun ℓ => discNormalizedKernel (fun ℓ => κF ℓ) κF.measurable ℓ) m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have hkappa : ∀ᵐ z ∂(volume.restrict (ball c r)), ∀ᵐ ω ∂P,
      κF (campbellReferenceObs γ 0 (ball c (2 * r)) (hC ω) z).2 (ball c (2 * r)) ≠ ⊤ :=
    ae_of_all _ fun z => ae_of_all _ fun ω =>
      ne_of_lt (lt_of_le_of_lt (ProbabilityTheory.Kernel.measure_le_bound κF _ _)
        (ProbabilityTheory.Kernel.bound_lt_top κF))
  exact href_discNormalized_doubledDisc hCM hB hG c hr hF hCC hU Dμ Dd hFdef (fun ℓ => κF ℓ) κF.measurable m₀ hCov
    m H hH hPH hagree hkappa

end HarmonicBalls.FirstPassS11iStep8HrefBall

#print axioms HarmonicBalls.FirstPassS11iStep8HrefBall.href_discNormalized_of_covariance
#print axioms HarmonicBalls.FirstPassS11iStep8HrefBall.canonical_frequency_eq_of_models
#print axioms HarmonicBalls.FirstPassS11iStep8HrefBall.href_discNormalized_doubledDisc
#print axioms HarmonicBalls.FirstPassS11iStep8HrefBall.href_discNormalized_doubledDisc_finiteKernel
