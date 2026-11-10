import HarmonicBalls.FirstPass.S11i.HzoomUnitBallFit
import HarmonicBalls.FirstPass.S11i.HzoomUnitBall
import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived

/-!
# Unit-ball frequency of every normalized LQG model, on the doubled disc (fp-S11i-hzoom-scale-e, n4)

`Step8UnitBallInputs2`: the inputs of the per-ball Step 8 route on the doubled disc (operator rulings of 2026-11-10 15:12 UTC):

* root disc `U_p = ball c r`, decoder disc `D_p = ball c (2 r)` (`c = ballCen p`, `r = ballRad p`);
* kernel `κ_p` and metric decoder `m_p 𝔇` (index: the LQG metric `𝔇` with `IsLQGMetric γ ξ 𝔇`), built in
  HzoomUnitBallDecoders.lean; fitting identity `hfit` in HzoomUnitBallFit.lean;
* `href` is a NAMED field (n3's doubled-disc instance, Step8HrefBall.lean, not yet posted);
* the frozen/approved inputs are the binders of `step8UnitBallInputs2_of`: `hK` (LocalMeasureKernelStmt), `hR`
  (LocalMetricReplacementStmt), `hfr`, `hPos` (frozen), `hgeo` (IsBufferedPinchGeometry: replaces the containment binders
  hCC, hU, hUm, hdelta, ruling B2), `hNat` (LQGMeasureNonatomic), `hA10` (DMSLemmaA10WholePlaneMarked).

The probability space is `Ω : Type` (not `Type u`): `rootedLengthProperty` (S11ah/RootedLengthProperty.lean:57) is stated for
`Ω : Type`. The corollary `unitBallFrequencyModels_of_inputs2` is `UnitBallFrequencyModelsStmt` (HzoomScale.lean:124) at the
given `q`; at `q = step8Frequency P γ hC₀ F` it is `unitBallFrequencyModels_at_step8Frequency`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit HarmonicBalls.FirstPassS11iHzoom FirstPassS11ai

namespace HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The inputs of the Step 8 unit-ball route on the doubled disc. `κ p`, `m 𝔇 p` live on the decoder disc
`ball (ballCen p) (2 * ballRad p)`; `hBad`, `href`, `hfit` are indexed by the LQG metric `𝔇` (ruling B1). -/
structure Step8UnitBallInputs2 (P : Measure Ω) (γ ξ q δ M : ℝ) (U V W T Q' Q : Set ℂ) where
  /-- Null atom of the LQG measure (approved input `LQGMeasureNonatomic`, Proposed/LQG.lean:77). -/
  hNat : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC' hcirc'
  /-- Marked identity `DMSLemmaA10WholePlaneMarked` (DMS Lemma A.10, frozen). -/
  hA10 : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
    DMSLemmaA10WholePlaneMarked P γ hC' hcirc' μ'
  /-- The normalized finite decoder kernel of the decoder disc `D_p`. -/
  κ : ∀ p : ℚ × ℚ × ℚ, FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p) → Measure ℂ
  /-- The metric decoder of the decoder disc `D_p`, for the LQG metric `𝔇`. -/
  m : ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ p : ℚ × ℚ × ℚ, FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p) → ℂ → ℂ → ℝ
  /-- Measurability of the local failure set (`measurableSet_ballBad`). -/
  hBad : ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ), ValidBall p →
    MeasurableSet (HarmonicBalls.ReferenceNullS11i.refBadWindowSet
      (localCertSeq (κ p) (m 𝔇 h𝔇 p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q)
  /-- NAMED: reference observations avoid the failure set at `q` (n3's `href`, Step8HrefBall.lean; doubled-disc instance
  pending). -/
  href : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇),
    IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → ∀ p : ℚ × ℚ × ℚ, ValidBall p →
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
        campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
          HarmonicBalls.ReferenceNullS11i.refBadWindowSet
            (localCertSeq (κ p) (m 𝔇 h𝔇 p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q
  /-- Fitting identity of the decoded and physical certificate events (`ae_eventually_ballFit`). -/
  hfit : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇),
    IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' →
    (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D' ω u v ∧
      ENNReal.ofReal (D' ω u v) = weylScaling (𝔇 (hC' ω)) ξ (fun x => -0 * Real.log ‖x‖) u v) →
    ∀ p : ℚ × ℚ × ℚ, ValidBall p → ∀ᵐ ω ∂P, ∀ z ∈ ball (ballCen p) (2 * ballRad p), ∀ᶠ n : ℕ in atTop,
      (FirstPassS11i.CertificateEvent (κ p (fun φ => fieldPairing 0 (hC' ω) φ.1))
          (m 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC' ω) φ.1)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          (FirstPassS11ah.certScale n) z ↔
        FirstPassS11i.CertificateEvent (μ' ω) (D' ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          (FirstPassS11ah.certScale n) z)

/-- **The inputs on the doubled disc, built from the local frozen inputs.** `κ`, `m`, `hBad`, `hfit` are the constructions of
HzoomUnitBallDecoders.lean and HzoomUnitBallFit.lean; `href` is the named input. -/
noncomputable def step8UnitBallInputs2_of {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ} [IsProbabilityMeasure P]
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hNat : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC' hcirc')
    (hA10 : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
      DMSLemmaA10WholePlaneMarked P γ hC' hcirc' μ')
    (href : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
      (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇),
      IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → ∀ p : ℚ × ℚ × ℚ, ValidBall p →
        ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
          campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
            HarmonicBalls.ReferenceNullS11i.refBadWindowSet
              (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q) :
    Step8UnitBallInputs2 P γ ξ q δ M U V W T Q' Q where
  hNat := hNat
  hA10 := hA10
  κ := fun p ℓ => ballKernel hγ0 hγ2 hK p ℓ
  m := fun 𝔇 h𝔇 p ℓ => ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ
  hBad := fun 𝔇 h𝔇 p hp => measurableSet_ballBad hγ0 hγ2 hK hR 𝔇 h𝔇 hgeo q p hp
  href := href
  hfit := fun hC' hcirc' μ' D' 𝔇 h𝔇 hG hμ hD p hp =>
    ae_eventually_ballFit hγ0 hγ2 hK hR hfr hPos hgeo h𝔇 hG hμ (hA10 hC' hcirc' μ')
      (by
        filter_upwards [hNat hC' hcirc' hG hγ0 hγ2 (lqgQ_pos hγ0) μ' hμ] with ω hω
        exact hω 0)
      hD p hp

/-- `canonicalUnitFrequency` is the step-8 frequency at the insertion `γ` (chat 243 Q3). -/
theorem canonicalUnitFrequency_eq_step8Frequency (P : Measure Ω) (γ : ℝ) (hC₀ : Ω → (ℂ → ℝ) → ℝ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7))) :
    HarmonicBalls.FirstPassS11iHzoomUnitBall.canonicalUnitFrequency P γ hC₀ F =
      HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency P γ hC₀ F := rfl

/-- **Unit-ball frequency for every whole-plane model** (`UnitBallFrequencyModelsStmt`), from the doubled-disc inputs
`Step8UnitBallInputs2` (`href` at `q` is the only remaining named input), through `unitBallFrequencyStmt_of_cover`
(Step8Exhaustion.lean:185) and `ae_unitScale_of_ball` (Step8Exhaustion.lean:155) on the root disc `ball c r`, with the
decoder disc `ball c (2 r)`. -/
theorem unitBallFrequencyModels_of_inputs2 [IsProbabilityMeasure P] {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (inp : Step8UnitBallInputs2 P γ ξ q δ M U V W T Q' Q) :
    UnitBallFrequencyModelsStmt P γ ξ q U V W T Q' Q δ M := by
  intro hC' hcirc' μ' D' hG hμ hD
  obtain ⟨𝔇, h𝔇, hDa⟩ := hD
  have hNon : ∀ᵐ ω ∂P, μ' ω {0} = 0 := by
    filter_upwards [inp.hNat hC' hcirc' hG hγ0 hγ2 (lqgQ_pos hγ0) μ' hμ] with ω hω
    exact hω 0
  refine unitBallFrequencyStmt_of_cover P q δ M U V W T Q' Q μ' D' hNon ?_
  intro p hp
  have hle : ballRad p ≤ 2 * ballRad p := by linarith [(validBall_facts hp).1]
  have hUB : ball (ballCen p) (ballRad p) ⊆ ball (0 : ℂ) 1 := fun x hx =>
    (validBall_facts hp).2.2.1 (Metric.ball_subset_closedBall (Metric.ball_subset_ball hle hx))
  have hUD : ball (ballCen p) (ballRad p) ⊆ ball (ballCen p) (2 * ballRad p) :=
    Metric.ball_subset_ball hle
  exact ae_unitScale_of_ball (P := P) (μ0 := μ') (μα := μ') (Dα := D') (hA10 := inp.hA10 hC' hcirc' μ')
    (hGFF := hG) (hμ0 := hμ) (hWeyl := localLQGInsertionWeylOffOrigin_derived) (hγ0 := hγ0) (hγ2 := hγ2)
    (hα := lqgQ_pos hγ0) (hμα := hμ) (hNon0 := hNon) (hNonα := hNon)
    (c₂ := ballCen p) (r₂ := 2 * ballRad p) (U := ball (ballCen p) (ballRad p)) (hUB := hUB) (hUD := hUD)
    (hU := measurableSet_ball) (q := q) (κ := inp.κ p) (m := inp.m 𝔇 h𝔇 p)
    (Ostar := pinchOmegaGeom W Q δ) (U' := U) (V := V) (W := W) (T := T) (Q' := Q') (Q := Q) (η := δ) (M := M)
    (hBad := inp.hBad 𝔇 h𝔇 p hp) (href := inp.href hC' hcirc' μ' 𝔇 h𝔇 hG hμ p hp)
    (hfit := inp.hfit hC' hcirc' μ' D' 𝔇 h𝔇 hG hμ hDa p hp)

/-- The unit-ball frequency of every whole-plane model at the step-8 frequency `q_F = step8Frequency P γ hC₀ F`
(chat 243 Q3: the insertion is `γ`). -/
theorem unitBallFrequencyModels_at_step8Frequency [IsProbabilityMeasure P] {γ ξ δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hC₀ : Ω → (ℂ → ℝ) → ℝ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (inp : Step8UnitBallInputs2 P γ ξ (HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency P γ hC₀ F) δ M
      U V W T Q' Q) :
    UnitBallFrequencyModelsStmt P γ ξ (HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency P γ hC₀ F)
      U V W T Q' Q δ M :=
  unitBallFrequencyModels_of_inputs2 hγ0 hγ2 inp

end HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled

#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled.unitBallFrequencyModels_of_inputs2
#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled.step8UnitBallInputs2_of
