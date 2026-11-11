import HarmonicBalls.FirstPass.S11i.Step8Exhaustion
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter

/-!
# Unit-ball frequency of every normalized LQG model (Step 8)

Plugs the named binders of the per-ball Step 8 route into `UnitBallFrequencyModelsStmt` (`HzoomScale.lean:124`).

* `Step8UnitBallInputs`: the named binders, with their exact types.
  (a) `hNat`: `LQGMeasureNonatomic` for every model (approved HB staged input, Proposed/LQG.lean:77, Fact 2.1 I).
  (c) `hA10`: `DMSLemmaA10WholePlaneMarked` for every model (frozen, Frozen/S11i.lean:39).
  (b) decoders `κ`, `m` per valid ball, and `hBad`, `href`, `hfit`: the binders of `ae_unitScale_of_ball`
      (Step8Exhaustion.lean:155), the Step 8 outputs.
* `unitBallFrequencyModels_of_inputs`: `UnitBallFrequencyModelsStmt` from these binders, through `unitBallFrequencyStmt_of_cover`.
* `unitBallFrequencyModels_at_canonical`: the same at the canonical value `canonicalUnitFrequency` (`qF`).
* `hzoom_all_of_inputs`, `hphys_of_inputs`: `hzoom_all_of_unit_models`, `hphys_of_unit_models` with the producer plugged in.

The null atom `μ' ω {0} = 0` is derived from `hNat`. The Weyl hypothesis `hWeyl` is the derived theorem
`localLQGInsertionWeylOffOrigin_derived` (S8c/WeylOffOriginDerived.lean), with no hypothesis.
Note: `hfit` is the eventual-in-`n` form of `ae_unitScale_of_ball` (commit d5dae0be); `UnitBallFrequencyModelsStmt`
(HzoomScale.lean:124) is unchanged, and its free `q` is instantiated at `canonicalUnitFrequency`.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal
open HarmonicBalls.S11c HarmonicBalls.FirstPassS11iStep8Transfer HarmonicBalls.FirstPassS11iStep8Corrected
open HarmonicBalls.FirstPassS11iStep8PhysicalWindow HarmonicBalls.FirstPassS11iStep8Zoom
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8Exhaustion FirstPassS11i FirstPassS11ai FirstPassS11ah

namespace HarmonicBalls.FirstPassS11iHzoomUnitBall

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The named binders of the per-ball Step 8 route, for every whole-plane model `(hC', hcirc', μ', D')` with
`IsWholePlaneGFF P hC' hcirc'`, `IsLQGMeasureOfField P γ 0 hcirc' μ'`, `IsLQGMetricOfField P γ ξ 0 hC' D'`. The decoders
`κ p`, `m p` live on the test-function space of the ball `ball (ballCen p) (ballRad p)`. `q` is the unit-ball limit. -/
structure Step8UnitBallInputs (P : Measure Ω) (γ ξ q δ M : ℝ) (U V W T Q' Q : Set ℂ) where
  /-- (a) Null atom, approved HB staged input `LQGMeasureNonatomic` (Proposed/LQG.lean:77, Fact 2.1 I), every model. -/
  hNat : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC' hcirc'
  /-- (c) Marked identity `DMSLemmaA10WholePlaneMarked` (DMS Lemma A.10, frozen), every model and every `μ'`. -/
  hA10 : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ),
    DMSLemmaA10WholePlaneMarked P γ hC' hcirc' μ'
  /-- (b) Decoder of the local measure on the ball of index `p`. -/
  κ : ∀ p : ℚ × ℚ × ℚ,
    ({φ : ℂ → ℝ // IsTestFunction (ball (ballCen p) (ballRad p)) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ
  /-- (b) Decoder of the local metric on the ball of index `p`. -/
  m : ∀ p : ℚ × ℚ × ℚ,
    ({φ : ℂ → ℝ // IsTestFunction (ball (ballCen p) (ballRad p)) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ
  /-- (b) Measurability of the local failure set (`ae_unitScale_of_ball` binder `hBad`). -/
  hBad : ∀ p : ℚ × ℚ × ℚ, ValidBall p →
    MeasurableSet (HarmonicBalls.ReferenceNullS11i.refBadWindowSet
      (localCertSeq (κ p) (m p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q)
  /-- (b) Reference observation avoids the failure set (`ae_unitScale_of_ball` binder `href`), every model. -/
  href : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → IsLQGMetricOfField P γ ξ 0 hC' D' →
    ∀ p : ℚ × ℚ × ℚ, ValidBall p →
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
        campbellReferenceObs γ 0 (ball (ballCen p) (ballRad p)) (hC' ω) z ∉
          HarmonicBalls.ReferenceNullS11i.refBadWindowSet
            (localCertSeq (κ p) (m p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q
  /-- (b) Fitting identity of the decoded and physical certificate events (`ae_unitScale_of_ball` binder `hfit`). -/
  hfit : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → IsLQGMetricOfField P γ ξ 0 hC' D' →
    ∀ p : ℚ × ℚ × ℚ, ValidBall p →
      ∀ᵐ ω ∂P, ∀ z ∈ ball (ballCen p) (ballRad p), ∀ᶠ n : ℕ in atTop,
        (FirstPassS11i.CertificateEvent (κ p (fun φ => fieldPairing 0 (hC' ω) φ.1))
            (m p (fun φ => fieldPairing 0 (hC' ω) φ.1)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M (certScale n) z ↔
          FirstPassS11i.CertificateEvent (μ' ω) (D' ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M (certScale n) z)

variable {P : Measure Ω} {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ}

/-- **Unit-ball frequency for every whole-plane model** (`UnitBallFrequencyModelsStmt`), from the named binders
`Step8UnitBallInputs`, through the per-ball cover `unitBallFrequencyStmt_of_cover` (Step8Exhaustion.lean:185). -/
theorem unitBallFrequencyModels_of_inputs [IsProbabilityMeasure P] (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (inp : Step8UnitBallInputs P γ ξ q δ M U V W T Q' Q) :
    UnitBallFrequencyModelsStmt P γ ξ q U V W T Q' Q δ M := by
  intro hC' hcirc' μ' D' hG hμ hD
  have hNon : ∀ᵐ ω ∂P, μ' ω {0} = 0 := by
    filter_upwards [inp.hNat hC' hcirc' hG hγ0 hγ2 (lqgQ_pos hγ0) μ' hμ] with ω hω
    exact hω 0
  refine unitBallFrequencyStmt_of_cover P q δ M U V W T Q' Q μ' D' hNon ?_
  intro p hp
  obtain ⟨hr, -, hc⟩ : 0 < ballRad p ∧ 2 * ballRad p < ‖ballCen p‖ ∧ ‖ballCen p‖ + 2 * ballRad p < 1 := id hp
  have hUB : ball (ballCen p) (ballRad p) ⊆ ball (0 : ℂ) 1 := by
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]
    linarith
  exact ae_unitScale_of_ball (P := P) (μ0 := μ') (μα := μ') (Dα := D') (hA10 := inp.hA10 hC' hcirc' μ')
    (hGFF := hG) (hμ0 := hμ) (hWeyl := localLQGInsertionWeylOffOrigin_derived) (hγ0 := hγ0) (hγ2 := hγ2)
    (hα := lqgQ_pos hγ0) (hμα := hμ) (hNon0 := hNon) (hNonα := hNon)
    (c₂ := ballCen p) (r₂ := ballRad p) (U := ball (ballCen p) (ballRad p)) (hUB := hUB)
    (hUD := subset_rfl) (hU := measurableSet_ball) (q := q) (κ := inp.κ p) (m := inp.m p)
    (Ostar := pinchOmegaGeom W Q δ) (U' := U) (V := V) (W := W) (T := T) (Q' := Q') (Q := Q) (η := δ) (M := M)
    (hBad := inp.hBad p hp) (href := inp.href hC' hcirc' μ' D' hG hμ hD p hp)
    (hfit := inp.hfit hC' hcirc' μ' D' hG hμ hD p hp)

/-- The canonical unit-ball limit `qF = (P {ω | alphaCanon α hC₀ ω ∈ F}).toReal` (the
limit in Step8Decoded.lean:80 is written with `alphaCanon γ`, see the report). -/
noncomputable def canonicalUnitFrequency (P : Measure Ω) (α : ℝ) (hC₀ : Ω → (ℂ → ℝ) → ℝ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : ℝ :=
  (P {ω | alphaCanon α hC₀ ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal

/-- `UnitBallFrequencyModelsStmt` at the canonical value `qF = canonicalUnitFrequency P α hC₀ F`. -/
theorem unitBallFrequencyModels_at_canonical [IsProbabilityMeasure P] (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) (hC₀ : Ω → (ℂ → ℝ) → ℝ) (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (inp : Step8UnitBallInputs P γ ξ (canonicalUnitFrequency P α hC₀ F) δ M U V W T Q' Q) :
    UnitBallFrequencyModelsStmt P γ ξ (canonicalUnitFrequency P α hC₀ F) U V W T Q' Q δ M :=
  unitBallFrequencyModels_of_inputs hγ0 hγ2 inp

/-- `hzoom_all_of_unit_models` (HzoomScale.lean:141) with the producer plugged in for `hunit`. -/
theorem hzoom_all_of_inputs [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (hMetric : ZoomMetricNormStmt P γ ξ hC hcirc D)
    (inp : Step8UnitBallInputs P γ ξ q δ M U V W T Q' Q) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) :=
  hzoom_all_of_unit_models hγ0 hγ2 hG hμ hCC hMetric (unitBallFrequencyModels_of_inputs hγ0 hγ2 inp)

/-- `hphys_of_unit_models` (HzoomScale.lean:173) with the producer plugged in for `hunit`. -/
theorem hphys_of_inputs [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (hMetric : ZoomMetricNormStmt P γ ξ hC hcirc D)
    (inp : Step8UnitBallInputs P γ ξ q δ M U V W T Q' Q) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) :=
  hphys_of_unit_models hγ0 hγ2 hG hμ hCC hMetric (unitBallFrequencyModels_of_inputs hγ0 hγ2 inp)

end HarmonicBalls.FirstPassS11iHzoomUnitBall

