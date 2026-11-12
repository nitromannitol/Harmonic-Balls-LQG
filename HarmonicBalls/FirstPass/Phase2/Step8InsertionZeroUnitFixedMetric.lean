import HarmonicBalls.FirstPass.Phase2.Step8HrefFixedMetric
import HarmonicBalls.FirstPass.Phase2.Step8InsertionZeroUnitSeed

/-!
# Step 8 of Lemma 11.13: insertion-zero unit frequency for one fixed LQG metric

The unit-ball frequency of the certificate events in an insertion-zero whole-plane model whose metric is the Weyl
scaling of one fixed LQG metric `𝔇₀` at the field of the model (no uniqueness of the LQG metric is used):

* `unitBallFrequency_of_href_fixedMetric`: for one model, from the reference-null field `href` at the ball decoders of
  `𝔇₀`, the local measure kernel `hK`, the local metric replacement `hR`, `hfr`, the positivity of the LQG measure of
  squares, the non-atomicity of the LQG measure and the marked whole-plane Lemma A.10 of Duplantier-Miller-Sheffield.
  It is the per-model, per-metric form of `unitBallFrequencyModels_of_inputs2` (`S11i/HzoomUnitBallDoubled.lean`):
  the covering of the unit disc by rational balls (`unitBallFrequencyStmt_of_cover`), the unit-scale frequency on each
  ball (`ae_unitScale_of_ball`), the ball decoders of `𝔇₀` and their fitting identity (`ae_eventually_ballFit`).
* `insertionZeroUnit_of_seed_fixedMetric`: for every such model and every common probability `q` of a coding event `E`
  satisfying the seed of Lemma 11.12 for the metric `𝔇₀`, the unit-ball frequency is `q`. The reference-null field is
  `hHref_of_seed_fixedMetric` (`Phase2/Step8HrefFixedMetric.lean`); the local measure kernel, the positivity of the LQG
  measure of squares, its non-atomicity and the marked Lemma A.10 are supplied by their proofs.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit HarmonicBalls.FirstPassS11iHzoom

namespace HarmonicBalls.FirstPassPhase2Step8InsertionZeroUnitFixedMetric

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassPhase2Step8HrefFixedMetric

/-- **Unit-ball frequency of one insertion-zero model, for one fixed LQG metric.** Let `𝔇₀` be an LQG metric and let
`D` be, almost surely, the Weyl scaling of `𝔇₀` at the field `hC` of a whole-plane insertion-zero model. If the
reference observations of every valid rational ball avoid the failure set at `q` of the ball decoders of `𝔇₀`
(`href`), then the certificate events of `(μ, D)` have unit-ball frequency `q`. -/
theorem unitBallFrequency_of_href_fixedMetric {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇₀)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) (lqgXi γ) (fun x => -0 * Real.log ‖x‖) u v)
    (hNat : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (href : ∀ p : ℚ × ℚ × ℚ, ValidBall p →
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
        campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z ∉
          HarmonicBalls.ReferenceNullS11i.refBadWindowSet
            (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p)
              (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q) :
    UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D := by
  have hNon : ∀ᵐ ω ∂P, μ ω {0} = 0 := by
    filter_upwards [hNat hG hγ0 hγ2 (lqgQ_pos hγ0) μ hμ] with ω hω
    exact hω 0
  refine unitBallFrequencyStmt_of_cover P q δ M U V W T Q' Q μ D hNon ?_
  intro p hp
  have hle : ballRad p ≤ 2 * ballRad p := by linarith [(validBall_facts hp).1]
  have hUB : ball (ballCen p) (ballRad p) ⊆ ball (0 : ℂ) 1 := fun x hx =>
    (validBall_facts hp).2.2.1 (Metric.ball_subset_closedBall (Metric.ball_subset_ball hle hx))
  have hUD : ball (ballCen p) (ballRad p) ⊆ ball (ballCen p) (2 * ballRad p) :=
    Metric.ball_subset_ball hle
  exact ae_unitScale_of_ball (P := P) (μ0 := μ) (μα := μ) (Dα := D) (hA10 := hA10)
    (hGFF := hG) (hμ0 := hμ) (hWeyl := localLQGInsertionWeylOffOrigin_derived) (hγ0 := hγ0) (hγ2 := hγ2)
    (hα := lqgQ_pos hγ0) (hμα := hμ) (hNon0 := hNon) (hNonα := hNon)
    (c₂ := ballCen p) (r₂ := 2 * ballRad p) (U := ball (ballCen p) (ballRad p)) (hUB := hUB) (hUD := hUD)
    (hU := measurableSet_ball) (q := q) (κ := fun ℓ => ballKernel hγ0 hγ2 hK p ℓ)
    (m := fun ℓ => ballMetric hγ0 hγ2 hR 𝔇₀ h𝔇₀ p ℓ)
    (Ostar := pinchOmegaGeom W Q δ) (U' := U) (V := V) (W := W) (T := T) (Q' := Q') (Q := Q) (η := δ) (M := M)
    (hBad := measurableSet_ballBad hγ0 hγ2 hK hR 𝔇₀ h𝔇₀ hgeo q p hp) (href := href p hp)
    (hfit := ae_eventually_ballFit hγ0 hγ2 hK hR hfr hPos hgeo h𝔇₀ hG hμ hA10 hNon hD p hp)

/-- **Insertion-zero unit frequency for one fixed LQG metric, from the seed of Lemma 11.12.** Let `𝔇₀` be an LQG metric
and `E` a measurable coding event satisfying the seed `hEq` for `𝔇₀` (in every insertion-`γ` model whose metric is,
almost surely, the Weyl scaling of `𝔇₀` at the field with the `γ`-log singularity, `E` holds for the local field on
`B(0,7)` if and only if the certificate event at radius `1` about `0` holds). Then in every whole-plane insertion-zero
model whose metric is, almost surely, the Weyl scaling of `𝔇₀` at its field, the certificate events have unit-ball
frequency `q` for every common probability `q` of `E`. The remaining inputs are `hR`, `hfr` and `hAx`. -/
theorem insertionZeroUnit_of_seed_fixedMetric {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇₀) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) (lqgXi γ) (fun x => -0 * Real.log ‖x‖) u v) →
      ∀ q : ℝ, CommonProb.{0} γ E q → UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D := by
  intro Ω _ P hC hcirc μ D hG hμ hD q hq
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  have hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂ :=
    fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂
  exact unitBallFrequency_of_href_fixedMetric hγ0 hγ2 hgeo hK hR hfr lqgMeasureSquarePositiveFrozen_holds.{0} h𝔇₀
    hG hμ hD (lqgMeasureNonatomic_holds.{0} Ω P γ 0 hC hcirc)
    (HarmonicBalls.dmsA10Marked_of_sub P γ hC hcirc μ
      (dmsLemmaA10WholePlaneMarkedSub_forall.{0} Ω P γ hC hcirc μ) hγ0 hγ2)
    (fun p hp => hHref_of_seed_fixedMetric hγ0 hγ2 hgeo hK hR hfr hAx h𝔇₀ hE hEq Ω P q hq hC hcirc μ hG hμ p hp)

end HarmonicBalls.FirstPassPhase2Step8InsertionZeroUnitFixedMetric
