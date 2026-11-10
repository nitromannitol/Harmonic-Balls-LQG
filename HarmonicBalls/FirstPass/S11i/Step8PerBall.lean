import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8Exhaustion
import HarmonicBalls.FirstPass.S11i.Step8Href

/-!
# Step 8: the per-ball unit-scale limit from the covariance input

Packages `ae_unitScale_of_ball` (`Step8Exhaustion.lean`) for one local ball `ball c₁ r₁ ⊆ ball c₂ r₂ ⊆ ball 0 1`
with its input `href` supplied by the covariance route (`ae_href_of_covariance`, `Step8Href.lean`) and the level
`q = P{α ∈ F}`. The remaining named inputs are the frozen Weyl relation and nonatomicity, the decoder measurability
`hmeas` (so that the bad window set is measurable), the fitting identity `hfit`, and the covariance input `hCov`
with the scale-one identification `hFdef`.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8PerBall

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c
open HarmonicBalls.FirstPassS11iStep8Transfer
open HarmonicBalls.FirstPassS11iStep8Corrected HarmonicBalls.FirstPassS11iStep8PhysicalWindow
open HarmonicBalls.FirstPassS11iHzoom FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iAnnularWeylAbsCont FirstPassS11at FirstPassS11i
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iStep8Href

/-- **Per-ball unit-scale limit.** For a local ball `ball c₁ r₁` with `closedBall c₁ r₁ ⊆ ball c₂ r₂` and
`ball c₁ r₁ ⊆ ball 0 1`, the unit-scale window frequency of the physical pair `(μα, Dα)` tends to `q = P{α ∈ F}`
at `μα`-a.e. `z ∈ ball c₁ r₁`, almost surely. -/
theorem ae_unitScale_of_covariance {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      CertificateEvent (Dμ L) (Dd L) Ostar U' V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U' V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (rootedMeasDec c₂ r₂ κ γ α₀ hC) (rootedMetricDec c₂ r₂ m γ α₀ hC) Dμ Dd)
    (hmeas : ∀ n, Measurable (localCertSeq κ m Ostar U' V W T Q' Q η M n))
    (hfit : ∀ᵐ ω ∂P, ∀ z ∈ ball c₂ r₂, ∀ᶠ n : ℕ in atTop,
      (CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball c₁ r₁ →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μα ω) (Dα ω) Ostar U' V W T Q' Q η M z N) atTop
        (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) := by
  have href := ae_href_of_covariance hCM hB hGFF hsub hF κ m Ostar U' V W T Q' Q η M Dμ Dd hFdef hCov
  exact ae_unitScale_of_ball μ0 μα Dα hA10 hGFF hμ0 hWeyl hγ0 hγ2 hα hμα hNon0 hNonα
    (ball c₁ r₁) hUB (ball_subset_closedBall.trans hsub) measurableSet_ball
    (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal κ m Ostar U' V W T Q' Q η M
    (ReferenceNullS11i.measurableSet_refBadWindowSet _ hmeas _) href hfit

end HarmonicBalls.FirstPassS11iStep8PerBall

#print axioms HarmonicBalls.FirstPassS11iStep8PerBall.ae_unitScale_of_covariance
