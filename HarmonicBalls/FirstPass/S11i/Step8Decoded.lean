import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8PerBall
import HarmonicBalls.FirstPass.S11i.Step8Fitting
import HarmonicBalls.FirstPass.S11i.Step8LengthMetric

/-!
# Step 8: the per-ball unit-scale limit with the decoded fitting identity discharged (fp-S11i-11-13f, n3)

`ae_unitScale_of_covariance` (`Step8PerBall.lean`) takes the fitting identity `hfit` as a named input. Here `hfit` is
produced from the decoder clauses:

* the mass clause `hκ` (decoded measure is a positive multiple of `μα` on `ball c₂ r₂`);
* the metric clause `hint`, in the form of `LocalMetricReplacementStmt` (`S11r/LocalMetricReplacement.lean`, clause (18)
  with `α = α₀`): the decoded metric is a positive multiple of the internal metric of the weylScaling metric
  `𝔇 (hC ω)` on `ball c₂ r₂`, where `Dα ω = (weylScaling (𝔇 (hC ω)) ξ (-α₀ log|·|)).toReal` a.s.;
* nonnegativity `hm0` of the decoder (the caller replaces the decoder `m` by `max m 0`, which keeps the `ENNReal`
  clause);
* Euclidean length metric of `Dα ω` a.s. (`Step8LengthMetric.lean`, from the Proposed input `LQGMetricFieldAxioms`).

The conclusion is the per-ball limit of `ae_unitScale_of_covariance`. The remaining named inputs are the covariance input
`hCov`, the decoder measurability `hmeas` (open: local decoders are not whole-plane length metrics), the scale-one
identification `hFdef`, the containment `hCC`, `U' ⊆ closedBall 0 7` (paper l.4009), and the frozen Weyl and
nonatomicity inputs.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Decoded

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c
open HarmonicBalls.FirstPassS11iStep8Transfer
open HarmonicBalls.FirstPassS11iStep8Corrected HarmonicBalls.FirstPassS11iStep8PhysicalWindow
open HarmonicBalls.FirstPassS11iHzoom FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iAnnularWeylAbsCont FirstPassS11at FirstPassS11i
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iStep8Href
open HarmonicBalls.FirstPassS11iStep8PerBall HarmonicBalls.FirstPassS11iStep8Fitting
open HarmonicBalls.FirstPassS11iStep8LengthMetric

/-- **Per-ball unit-scale limit from the decoder clauses.** Same conclusion as `ae_unitScale_of_covariance`, with the
fitting identity replaced by the decoder clauses `hκ`, `hm0`, `hint`, and the metric data `hL`, `hDω`, `hFact`. -/
theorem ae_unitScale_of_decoded_ball {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      CertificateEvent (Dμ L) (Dd L) Ostar U' V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hCov : RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ Set.univ
      Ostar U' V W T Q' Q η M (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
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
  exact ae_unitScale_of_covariance hCM hB hGFF μ0 μα Dα hA10 hμ0 hWeyl hγ0 hγ2 hα hμα hNon0 hNonα hsub hUB hF
    κ m Ostar U' V W T Q' Q η M Dμ Dd hFdef hCov hmeas hfit

end HarmonicBalls.FirstPassS11iStep8Decoded

#print axioms HarmonicBalls.FirstPassS11iStep8Decoded.ae_unitScale_of_decoded_ball
