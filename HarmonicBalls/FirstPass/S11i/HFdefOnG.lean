import HarmonicBalls.FirstPass.S11ax
import HarmonicBalls.FirstPass.S11m.CertificateAssembly
import HarmonicBalls.FirstPass.S11i.Step8Calibration
import HarmonicBalls.FirstPass.S11i.RootedLocality
import HarmonicBalls.FirstPass.S11ai.RootedCertSpecialized
import HarmonicBalls.FirstPass.S11i.Step8Href
import HarmonicBalls.FirstPass.S11i.Step8PerBall
import HarmonicBalls.FirstPass.S11i.Step8Decoded
import HarmonicBalls.FirstPass.S11i.Step8LengthMetric
import HarmonicBalls.FirstPass.S11i.Step8Fitting

/-!
# The coding identity `hFdef` on the canonical support `G`

`hFdef` is required only on the canonical support `G` (`S11r/RootedHrefBall.lean`, `RootedHrefBallStructure.lean`), not for every code `L`.

## Part 1: the identity on `G` for the Lemma 11.12 coding set

For the coding set `E := decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M` with decoders
`Ψc` (metric) and `Φμ` (measure) on the code space `ModConstTestPairings (ball 0 7)`, and `Dμ L := Φμ (ballRestrictPairing 7 L)`,
`Dd L := Ψc (ballRestrictPairing 7 L)`, the identity `hFdef` holds for `L ∈ G` by `certificateEvent_iff_pinchLocalRule`
(`S11i/Step8Calibration.lean:35`) and `decodedPinchRule_iff_ball` (`S11ax.lean`, `b = c = 1`). The G-properties used,
to be delivered for every `L ∈ G`:
* `hmet`: `IsEuclideanLengthMetric (Ψc (ballRestrictPairing 7 L))` and `0 ≤ Ψc (ballRestrictPairing 7 L) x y`;
* `hdec`: `DecodesOnSetsBall I (decodedFamily Ψc) (Ψc (ballRestrictPairing 7 L)) 1 (ballRestrictPairing 7 L)`;
* `hfin`: `annulusGreenPotentialSup (Φμ (ballRestrictPairing 7 L)) 0 3 6 ≠ ⊤` and `Φμ (ballRestrictPairing 7 L) U ≠ ⊤`.

## Part 2: G-variants of the consumers of `hFdef`

Each consumer takes `hFdef` for all `L`. Its G-variant takes `G`, `hFdefG : ∀ L ∈ G, ...` and the rooted membership
`hGroot`: almost surely, every rooted pairing `dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))`
(for `z ∈ ball c₁ r₁`, admissible shift `(b, u)`, all `n`) lies in `G`. This is the decoded observation lying in `G` a.s.
`hGroot` is a NAMED hypothesis: it must be delivered (rooted translation and shift invariance of `G`);
it is not derived here. The leaf uses `hFdef` only at the rooted pairing (`S11ai/RootedCertSpecialized.lean:86`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls.FirstPassS11iHFdefOnG

open HarmonicBalls HarmonicBalls.S11ax HarmonicBalls.S11m HarmonicBalls.S11m.CertificateAssembly
open FirstPassS11i HarmonicBalls.S11i.Step8Calibration

/-- **Coding identity on the canonical support (Part 1).** For `L ∈ G`, the scale-one certificate event of the decoded pair
at centre `0` holds iff `ballRestrictPairing 7 L` lies in the Lemma 11.12 coding set `E`. -/
theorem hFdef_decoded_on_G {U V W T Q' Q : Set ℂ} {δ M : ℝ}
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ)
    (I : HarmonicBalls.S11am.PinchCountSets V W T Q' Q δ)
    (Ψc : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ → ℂ → ℝ)
    (Φμ : ModConstTestPairings (ball (0 : ℂ) 7) → Measure ℂ)
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (Ψc (ballRestrictPairing 7 L)) ∧
      ∀ x y : ℂ, 0 ≤ Ψc (ballRestrictPairing 7 L) x y)
    (hdec : ∀ L ∈ G, DecodesOnSetsBall I (decodedFamily Ψc) (Ψc (ballRestrictPairing 7 L)) 1
      (ballRestrictPairing 7 L))
    (hfin : ∀ L ∈ G, annulusGreenPotentialSup (Φμ (ballRestrictPairing 7 L)) 0 3 6 ≠ ⊤ ∧
      Φμ (ballRestrictPairing 7 L) U ≠ ⊤) :
    ∀ L ∈ G, CertificateEvent (Φμ (ballRestrictPairing 7 L)) (Ψc (ballRestrictPairing 7 L))
        (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0 ↔
      ballRestrictPairing 7 L ∈ decodedPinchRuleBall I (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) M := by
  intro L hL
  have hmS : decGreen Φμ (ballRestrictPairing 7 L) =
      ENNReal.ofReal 1 * annulusGreenPotentialSup (Φμ (ballRestrictPairing 7 L)) 0 3 6 := by
    simp [decGreen]
  have hmU : decMassU Φμ U (ballRestrictPairing 7 L) = ENNReal.ofReal 1 * Φμ (ballRestrictPairing 7 L) U := by
    simp [decMassU]
  have hiff := decodedPinchRule_iff_ball (hmet L hL).1 (hmet L hL).2 one_pos one_pos hgeo hΩ I
    (decodedFamily Ψc) (decGreen Φμ) (decMassU Φμ U) (Φμ (ballRestrictPairing 7 L)) M (ballRestrictPairing 7 L)
    (hdec L hL) hmS hmU
  rw [certificateEvent_iff_pinchLocalRule, hiff]
  exact ⟨fun h => ⟨h, (hfin L hL).1, (hfin L hL).2⟩, fun h => h.1⟩

end HarmonicBalls.FirstPassS11iHFdefOnG

namespace HarmonicBalls.FirstPassS11iHFdefOnGChain

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah FirstPassS11at FirstPassS11i
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iStep8Href
open HarmonicBalls.FirstPassS11iStep8PerBall HarmonicBalls.FirstPassS11iStep8Decoded
open HarmonicBalls.FirstPassS11iStep8Transfer HarmonicBalls.FirstPassS11iStep8Corrected
open HarmonicBalls.FirstPassS11iStep8PhysicalWindow HarmonicBalls.FirstPassS11iHzoom
open HarmonicBalls.FirstPassS11iStep8LengthMetric HarmonicBalls.FirstPassS11iStep8Fitting

/-- **Leaf, on `G`.** `rootedCertTermwise_of_decoded` with `hFdef` replaced by `hFdefG` (on `G`) and the rooted membership
`hGroot`. The only use of `hFdef` in the original is at the rooted pairing `RootedCertSpecialized.lean:86`. -/
theorem rootedCertTermwise_of_decoded_G {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hFdefG : ∀ L ∈ G, FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔
      ballRestrictPairing 7 L ∈ F)
    (hGroot : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)) ∈ G) :
    RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ m Ostar U V W T Q' Q η M := by
  have hG := hGroot.mono fun z hz hzA b u hadm => (hz hzA b u hadm).mono fun ω hω n => hFdefG _ (hω n)
  exact ae_termwise_of_identification (F := F) hsub A Ostar U V W T Q' Q η M κ m
    (localCertSeq κ m Ostar U V W T Q' Q η M) (fun _ _ _ => rfl) Dμ Dd hCov hG

/-- **`ae_href_of_covariance` on `G`** (`S11i/Step8Href.lean:56`), with `hFdef` replaced by `hFdefG` and `hGroot`
(for `A = Set.univ`). -/
theorem ae_href_of_covariance_G {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hFdefG : ∀ L ∈ G, FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔
      ballRestrictPairing 7 L ∈ F)
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
    (hGroot : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ (Set.univ : Set ℂ) → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)) ∈ G) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball c₁ r₁ → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U V W T Q' Q η M)
          (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal := by
  have hT := rootedCertTermwise_of_decoded_G hsub Set.univ F κ m Ostar U V W T Q' Q η M Dμ Dd hCov G hFdefG hGroot
  have h := ae_href_of_termwise hCM hB hh Set.univ hF κ m Ostar U V W T Q' Q η M hT
  rw [ae_restrict_iff' measurableSet_ball] at h
  exact h.mono fun z hz hzB => hz hzB (mem_univ z)

/-- **`ae_unitScale_of_covariance` on `G`** (`S11i/Step8PerBall.lean:31`). -/
theorem ae_unitScale_of_covariance_G {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ0 μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hWeyl : HarmonicBalls.LocalLQGInsertionWeylOffOrigin.{u}) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (hUB : ball c₁ r₁ ⊆ ball (0 : ℂ) 1)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U' V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hFdefG : ∀ L ∈ G, CertificateEvent (Dμ L) (Dd L) Ostar U' V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U' V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
    (hGroot : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ (Set.univ : Set ℂ) → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)) ∈ G)
    (hmeas : ∀ n, Measurable (localCertSeq κ m Ostar U' V W T Q' Q η M n))
    (hfit : ∀ᵐ ω ∂P, ∀ z ∈ ball c₂ r₂, ∀ᶠ n : ℕ in atTop,
      (CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball c₁ r₁ →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μα ω) (Dα ω) Ostar U' V W T Q' Q η M z N) atTop
        (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) := by
  have href := ae_href_of_covariance_G hCM hB hGFF hsub hF κ m Ostar U' V W T Q' Q η M Dμ Dd G hFdefG hCov hGroot
  exact ae_unitScale_of_ball μ0 μα Dα hA10 hGFF hμ0 hWeyl hγ0 hγ2 hα hμα hNon0 hNonα
    (ball c₁ r₁) hUB (ball_subset_closedBall.trans hsub) measurableSet_ball
    (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal κ m Ostar U' V W T Q' Q η M
    (ReferenceNullS11i.measurableSet_refBadWindowSet _ hmeas _) href hfit

/-- **`ae_unitScale_of_decoded_ball` on `G`** (`S11i/Step8Decoded.lean:43`), with `hFdef` replaced by `hFdefG` and the rooted
membership `hGroot`. Body as in the original; the final call is `ae_unitScale_of_covariance_G`. -/
theorem ae_unitScale_of_decoded_ball_G {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (μ0 μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hWeyl : HarmonicBalls.LocalLQGInsertionWeylOffOrigin.{u}) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (hUB : ball c₁ r₁ ⊆ ball (0 : ℂ) 1)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U' V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (G : Set (ModConstTestPairings (Set.univ : Set ℂ)))
    (hFdefG : ∀ L ∈ G, CertificateEvent (Dμ L) (Dd L) Ostar U' V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U' V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
    (hGroot : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ (Set.univ : Set ℂ) → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)) ∈ G)
    (hmeas : ∀ n, Measurable (localCertSeq κ m Ostar U' V W T Q' Q η M n))
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hL : IsLQGMetric γ ξ 𝔇)
    (hFact : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hDω : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ Dα ω u v ∧
      ENNReal.ofReal (Dα ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U' ⊆ closedBall 0 7)
    (hκ : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (ball c₂ r₂) =
        ENNReal.ofReal a • (μα ω).restrict (ball c₂ r₂))
    (hm0 : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ m (fun φ => fieldPairing α₀ (hC ω) φ.1) x y)
    (hMet : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      ENNReal.ofReal (m (fun φ => fieldPairing α₀ (hC ω) φ.1) x y) =
        ENNReal.ofReal b * internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) (ball c₂ r₂) x y) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball c₁ r₁ →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μα ω) (Dα ω) Ostar U' V W T Q' Q η M z N) atTop
        (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) := by
  have hDn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dα ω x y := by
    filter_upwards [hDω] with ω hω
    exact fun x y => (hω x y).1
  have hLen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dα ω) :=
    ae_isEuclideanLengthMetric_of_fieldAxioms hFact hGFF hγ0 hγ2 hα hL hDω
  have hEq := ae_eq_toReal_weylScaling hDω
  have hMetA : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      ENNReal.ofReal (m (fun φ => fieldPairing α₀ (hC ω) φ.1) x y) =
        ENNReal.ofReal b * internalMetric (Dα ω) (ball c₂ r₂) x y := by
    filter_upwards [hMet, hEq] with ω hω hωeq
    obtain ⟨b, hb, h⟩ := hω
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    rw [hωeq]
    exact h x hx y hy
  have hfit := ae_fitting_eventually_of_decoders α₀ η M Ostar U' V W T Q' Q c₂ r₂ hC μα Dα κ m hCC hU hκ hm0
    hDn hLen hMetA
  exact ae_unitScale_of_covariance_G hCM hB hGFF μ0 μα Dα hA10 hμ0 hWeyl hγ0 hγ2 hα hμα hNon0 hNonα hsub hUB hF
    κ m Ostar U' V W T Q' Q η M Dμ Dd G hFdefG hCov hGroot hmeas hfit

end HarmonicBalls.FirstPassS11iHFdefOnGChain

