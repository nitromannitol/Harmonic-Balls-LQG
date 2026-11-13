import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11i.Step8Event
import HarmonicBalls.FirstPass.S11i.Step8ZoomFrequency
import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S11i.ZoomMetricAlpha0

/-!
# Step 8 physical frequency with an existential event

The counted consumer `Step8IdentityGivenPinchEventCanonicalStmt` needs the physical frequency for one choice of the
pinch event. This file gives the existential provider and its adapter.

* `Step8PhysExistsStmt.{v}`: from a pinch event, there is a pinch event `E` such that for every common
  probability `q` of `E`, the physical frequency holds at every scale `k` for all insertion-`α` models (`AllModelsAt`).
* `step8Identity_given_pinchEvent_canonical_of_physExists` (no binder beyond the provider): the common
  probability of `E` is `exists_localModConstField_prob`, the second conjunct is `step8_zoom_family_of_ae_frequency`.
* Route 2 (universe 0): `Step8PhysExistsStmt.{0}` from
  (a) `allModelsAt_zero_of_unit` (PROVED): insertion-zero physical frequency for every scale from the insertion-zero unit
      statement, via `hphys_of_unit_models`, `zoomMetricNormStmt_of_isLQGMetricOfField` (α = 0, proved),
      and the coordinate change `CoordChangeZeroStmt` (Proposed, Fact 2.1 IV);
  (b) `Step8InsertionTransferStmt` (NAMED BINDER): insertion-zero to insertion-`α` for `AllModelsAt`;
  (c) `Step8EventCalibrationStmt` (NAMED BINDER): a pinch event `E` calibrated to a coding event `F` whose
      insertion-zero unit frequency is its own probability.
  No singular α metric normalization (`hMet`) is used.

Universe. `AllModelsAt.{v}` quantifies over `Ω : Type v`. The insertion-zero step (a) uses the metric zoom
`zoomMetricNormStmt_of_isLQGMetricOfField`, which is stated for `Ω₀ : Type`, because `IsLQGMetric` quantifies its axioms
over `Ω : Type` (`Defs/LQGMetric.lean:181`). So route 2 gives `Step8PhysExistsStmt.{0}` only. The closure statements
(`Closure/Sec11Canonical.lean:77`, `Main12Canonical.lean:146`, `PaperExponent.lean:64`) take `hId` at a general universe `u`.
That gap is open and is stated in the report.

The identities `F = E` and `EventCalibration` are not definitional: `CommonProb` is a model-level equation, and the
premise event is not the coding event. The provider therefore chooses its event (no universal quantifier over events).
-/

universe v

namespace HarmonicBalls.FirstPassS11iStep8PhysExists

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8Zoom
open scoped ENNReal

/-- The Lemma 11.12 code space: pinch events are subsets of `ModConstTestPairings B₇`. -/
abbrev Step8Code := ModConstTestPairings (ball (0 : ℂ) 7)

/-- `CommonProb γ E q`: the canonical probability `P{localModConstField γ h B₇ ∈ E}` equals `q` in every whole-plane
model (Armstrong-Kuusi-Mourrat style model independence, `localModConstField_prob_indep`). -/
def CommonProb.{w} (γ : ℝ) (E : Set Step8Code) (q : ℝ) : Prop :=
  ∀ (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q

/-- `PhysicalAt P q U V W T Q' Q δ M k μ D`: almost surely, for `μ`-almost every centre `z ∈ B_{2^k}(0)`, the window
frequency of the certificate events (`pinchOmegaGeom W Q δ`, `η = δ`) at radii `2^k 2^{-n}` tends to `q`. -/
def PhysicalAt.{w} {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) (q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (k : ℕ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)

/-- `AllModelsAt γ ξ α q U V W T Q' Q δ M k`: `PhysicalAt` holds at scale `2^k` for every insertion-`α` LQG model on every
probability space `Ω : Type w` and every law `P` (uniformity over laws is explicit: the Cameron-Martin step of the insertion
transfer changes the law). -/
def AllModelsAt.{w} (γ ξ α q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (k : ℕ) : Prop :=
  ∀ (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
      PhysicalAt P q U V W T Q' Q δ M k μ D

/-- `EventCalibration γ E F`: `E` and `F` have the same common probability. -/
def EventCalibration.{w} (γ : ℝ) (E F : Set Step8Code) : Prop :=
  ∀ q : ℝ, CommonProb.{w} γ E q → CommonProb.{w} γ F q

/-- **Insertion-zero unit frequency of a coding event `F`** (route 2, universe `w`). For every insertion-zero model and every
`q` that is the common probability of `F`, the unit-ball frequency of the certificate events is `q`. The coding identity of
`F` (its `hFdef`, `S11i/Step8Decoded.lean:43`) and the unit-scale producer (`unitBallFrequencyModels_at_step8Frequency`,
`S11i/HzoomUnitBallDoubled.lean`) are its content. -/
def InsertionZeroUnitStmt.{w} (γ : ℝ) (F : Set Step8Code) (U V W T Q' Q : Set ℂ) (δ M : ℝ) : Prop :=
  ∀ (Ω : Type w) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) 0 hC D →
      ∀ q : ℝ, CommonProb.{w} γ F q → UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D

/-- **NAMED BINDER (route 2, (b)): insertion transfer of the physical frequency** (`allModelsAt_insertion_of_zero`). From insertion zero to insertion `α < Q_γ`, for every scale `k`, uniformly over laws.
Source: the local Cameron-Martin argument with `localLQGInsertionWeylOffOrigin_derived`,
`ae_fitting_eventually_of_decoders`, `ae_unitScale_of_decoded_ball`, `ae_forall_of_cover`. -/
def Step8InsertionTransferStmt : Prop :=
  ∀ (γ α q δ M : ℝ) (U V W T Q' Q : Set ℂ) (k : ℕ), IsBufferedPinchGeometry U V W T Q' Q δ →
    0 < γ → γ < 2 → α < lqgQ γ →
    AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M k → AllModelsAt.{0} γ (lqgXi γ) α q U V W T Q' Q δ M k

/-- The coordinate change of the LQG measure at insertion zero for every whole-plane model (`LQGMeasureCoordChange`, Proposed input, Fact 2.1 IV, `Proposed/LQG.lean:116`). -/
def CoordChangeZeroStmt : Prop :=
  ∀ (γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc

/-- **NAMED BINDER (route 2, (c)): event calibration**. From the existence of some pinch event at `γ`, there is
a pinch event `E` and a coding event `F` with the same common probability (`EventCalibration`), and `F` has the insertion-zero
unit frequency `InsertionZeroUnitStmt`. The probability of `F` is not prescribed in advance: `E` is chosen so that the
calibration holds. -/
def Step8EventCalibrationStmt.{w} : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ M γ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
    0 < γ → γ < 2 → 0 < M →
    (∃ E : Set Step8Code, PinchEventGammaCanonicalStmt.{w} U T Q' Q γ M E) →
    ∃ E F : Set Step8Code, PinchEventGammaCanonicalStmt.{w} U T Q' Q γ M E ∧ EventCalibration.{w} γ E F ∧
      InsertionZeroUnitStmt.{w} γ F U V W T Q' Q δ M

/-- **Existential provider.** From the existence of a pinch event, there is a pinch event `E` such
that every common probability `q` of `E` gives the physical frequency at every scale, for every insertion-`α` model. -/
def Step8PhysExistsStmt.{w} : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
    ∀ γ α M : ℝ, 0 < γ → γ < 2 → α < lqgQ γ → 0 < M →
    (∃ E : Set Step8Code, PinchEventGammaCanonicalStmt.{w} U T Q' Q γ M E) →
    ∃ E : Set Step8Code, PinchEventGammaCanonicalStmt.{w} U T Q' Q γ M E ∧
      ∀ q : ℝ, CommonProb.{w} γ E q → ∀ k : ℕ, AllModelsAt.{w} γ (lqgXi γ) α q U V W T Q' Q δ M k

/-- **Consumer adapter.** The corrected existential provider gives the counted consumer
`Step8IdentityGivenPinchEventCanonicalStmt`: the common probability of the selected event comes from
`exists_localModConstField_prob`, and the zoom family from `step8_zoom_family_of_ae_frequency`. -/
theorem step8Identity_given_pinchEvent_canonical_of_physExists.{w} (hPhys : Step8PhysExistsStmt.{w}) :
    Step8IdentityGivenPinchEventCanonicalStmt.{w} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM hE
  obtain ⟨E, hPG, hall⟩ := hPhys U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM hE
  refine ⟨E, hPG, ?_⟩
  unfold Step8IdentityCanonicalStmt Step8IdentityStmt
  obtain ⟨q, hq⟩ := HarmonicBalls.exists_localModConstField_prob γ hPG.1
  refine ⟨q, fun Ω _ P hC hcirc μ D hG _ _ => hq Ω P hC hcirc hG, ?_⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact HarmonicBalls.FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ₀ M q μ D
    (fun k => hall q hq k Ω P hC hcirc μ D hG hμ hD)

/-- **(a) Insertion-zero physical frequency at every scale from the insertion-zero unit statement** (route 2, universe 0).
For each insertion-zero model, `hphys_of_unit_models` (`S11i/HzoomScale.lean:173`) gives the zoom at every scale from the
unit-ball frequency of the normalized models; the metric normalization is `zoomMetricNormStmt_of_isLQGMetricOfField`
(`S11i/HzoomScale.lean:275`, proved for `Ω : Type`) and the coordinate change is `CoordChangeZeroStmt`. -/
theorem allModelsAt_zero_of_unit {γ q δ M : ℝ} {U V W T Q' Q : Set ℂ} {F : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hCC0 : CoordChangeZeroStmt)
    (hU : InsertionZeroUnitStmt.{0} γ F U V W T Q' Q δ M) (hq : CommonProb.{0} γ F q) (k : ℕ) :
    AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M k := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  unfold PhysicalAt
  have hunit : UnitBallFrequencyModelsStmt P γ (lqgXi γ) q U V W T Q' Q δ M :=
    fun hC' hcirc' μ' D' h1 h2 h3 => hU Ω P hC' hcirc' μ' D' h1 h2 h3 q hq
  exact (hphys_of_unit_models hγ0 hγ2 hG hμ (hCC0 γ Ω P hC hcirc)
    (zoomMetricNormStmt_of_isLQGMetricOfField hG hD) hunit) k

/-- **Route 2 (universe 0): `Step8PhysExistsStmt.{0}` from (a), (b), (c).** Take the pinch event `E` of the calibration
binder (c); for each common probability `q` of `E`, calibration gives the coding probability of `F`, (a) gives the
insertion-zero physical frequency at every scale, and (b) transfers it to insertion `α`. -/
theorem step8PhysExists_of_route2 (hCC0 : CoordChangeZeroStmt) (hCal : Step8EventCalibrationStmt.{0})
    (hIns : Step8InsertionTransferStmt) : Step8PhysExistsStmt.{0} := by
  intro U V W T Q' Q δ hgeom γ α M hγ0 hγ2 hα hM hE
  obtain ⟨E, F, hPG, hcal, hU⟩ := hCal U V W T Q' Q δ M γ hgeom hγ0 hγ2 hM hE
  refine ⟨E, hPG, fun q hq k => ?_⟩
  exact hIns γ α q δ M U V W T Q' Q k hgeom hγ0 hγ2 hα
    (allModelsAt_zero_of_unit hγ0 hγ2 hCC0 hU (hcal q hq) k)

/-- **Route 2 consumer (universe 0):** `Step8IdentityGivenPinchEventCanonicalStmt.{0}` from the three inputs (a) (proved),
(b) `hIns` and (c) `hCal`, and the Proposed coordinate change `hCC0`. -/
theorem step8Identity_given_pinchEvent_canonical_of_route2 (hCC0 : CoordChangeZeroStmt)
    (hCal : Step8EventCalibrationStmt.{0}) (hIns : Step8InsertionTransferStmt) :
    Step8IdentityGivenPinchEventCanonicalStmt.{0} :=
  step8Identity_given_pinchEvent_canonical_of_physExists (step8PhysExists_of_route2 hCC0 hCal hIns)

/-! ### Route 1: scale transfer at insertion `α` by normalization

Route 1 gives the scale `k` of the insertion-`α` statement from the scale-`0` statement of the normalized
insertion-`α` model. The normalization is `normMeasureAlpha` (measure, `Q - α` coefficient, `S11i/Step8PhysReduction.lean`) and
`zoomMetricNormAlpha_of_isLQGMetricOfField` (metric, `S11i/ZoomMetricAlpha0.lean`). The only insertion transfer needed is at
`k = 0`, the named binder `Step8InsertionTransferK0Stmt`. No decoder outside `ball 0 1` is used. -/

/-- **NAMED BINDER (route 1, k = 0 insertion transfer).** `Step8InsertionTransferStmt` at the unit scale only: the
insertion-zero scale-`0` statement implies the insertion-`α` scale-`0` statement. Until `allModelsAt_insertion_of_zero_k0`
lands, this Prop is the input. -/
def Step8InsertionTransferK0Stmt : Prop :=
  ∀ (γ α q δ M : ℝ) (U V W T Q' Q : Set ℂ), IsBufferedPinchGeometry U V W T Q' Q δ →
    0 < γ → γ < 2 → α < lqgQ γ →
    AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0 → AllModelsAt.{0} γ (lqgXi γ) α q U V W T Q' Q δ M 0

/-- At the scale `k = 0` the physical statement is the unit-ball frequency (`2^0 = 1`). -/
theorem physicalAt_zero_of_unitBall {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D) :
    PhysicalAt P q U V W T Q' Q δ M 0 μ D := by
  unfold UnitBallFrequencyStmt at h
  unfold PhysicalAt
  simpa only [pow_zero, one_mul] using h

/-- The insertion-zero unit frequency gives the insertion-zero statement at scale `0`. -/
theorem allModelsAt_zero_scale_zero_of_unit {γ q δ M : ℝ} {U V W T Q' Q : Set ℂ} {F : Set Step8Code}
    (hU : InsertionZeroUnitStmt.{0} γ F U V W T Q' Q δ M) (hq : CommonProb.{0} γ F q) :
    AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0 := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact physicalAt_zero_of_unitBall (hU Ω P hC hcirc μ D hG hμ hD q hq)

/-- **Route 1 zoom (insertion `α`).** For a fixed insertion-`α` model, the unit-ball frequency of every zoomed pair
`(a · zoomMeasure μ k, b · zoomMetric D k)` holds almost surely, given the scale-`0` statement `h0` at insertion `α` applied to
the normalized model `(normField 2^k, normCirc 2^k, normMeasureAlpha, Dk)`. The constants are `a = e^{γ · (-C_{α,2^k})}` and
`b = B⁻¹`, with `B` from `zoomMetricNormAlpha_of_isLQGMetricOfField`. -/
theorem hzoom_alpha_all_of_scale_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {D : Ω → ℂ → ℂ → ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D) (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (h0 : AllModelsAt.{0} γ ξ α q U V W T Q' Q δ M 0) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  intro k
  obtain ⟨Dk, hDk, hscale⟩ :=
    HarmonicBalls.FirstPassS11iZoomMetricAlpha0.zoomMetricNormAlpha_of_isLQGMetricOfField hG hD k
  have hR : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hGk := isWholePlaneGFF_normalized hG hR
  have hμk := HarmonicBalls.FirstPassS11iStep8PhysReduction.isLQGMeasureOfField_normMeasureAlpha
    hγ0 hγ2 hα hG hμ hCC k
  have hU := h0 Ω P (normField ((2 : ℝ) ^ k) hC hcirc) (normCirc ((2 : ℝ) ^ k) hcirc)
    (HarmonicBalls.FirstPassS11iStep8PhysReduction.normMeasureAlpha γ α μ hcirc k) Dk hGk hμk hDk
  unfold PhysicalAt at hU
  filter_upwards [hU, hscale] with ω hω hsc
  obtain ⟨B, hB, hBeq⟩ := hsc
  have hmet : (fun x y => B⁻¹ * zoomMetric (D ω) k x y) = Dk ω := by
    funext x y
    rw [hBeq x y, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]
  refine ⟨Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k)))), B⁻¹,
    Real.exp_pos _, inv_pos.mpr hB, ?_⟩
  have hmeas : ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 +
      (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k))))) • zoomMeasure (μ ω) k =
      HarmonicBalls.FirstPassS11iStep8PhysReduction.normMeasureAlpha γ α μ hcirc k ω := rfl
  rw [hmeas, hmet]
  simp only [pow_zero, one_mul] at hω
  exact hω

/-- **Route 1: every scale at insertion `α`.** The scale-`0` insertion-`α` statement implies the statement at every scale `k`
(`hphys_of_zoom_const_family` applied to `hzoom_alpha_all_of_scale_zero`). -/
theorem allModelsAt_all_scales_of_scale_zero {γ ξ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (h0 : AllModelsAt.{0} γ ξ α q U V W T Q' Q δ M 0) (k : ℕ) :
    AllModelsAt.{0} γ ξ α q U V W T Q' Q δ M k := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  unfold PhysicalAt
  exact (HarmonicBalls.FirstPassS11iStep8Transfer.hphys_of_zoom_const_family P U V W T Q' Q δ M q μ D
    (hzoom_alpha_all_of_scale_zero hγ0 hγ2 hα hG hμ hD (hCCα γ α Ω P hC hcirc) h0)) k

/-- **Route 1 (universe 0): `Step8PhysExistsStmt.{0}`.** Take the pinch event `E` of the calibration binder (c); for each common
probability `q` of `E`, calibration gives the coding event `F` with the insertion-zero unit frequency, which gives the scale-`0`
insertion-zero statement; the k = 0 transfer (binder `Step8InsertionTransferK0Stmt`) gives the scale-`0` insertion-`α`
statement; route 1 gives every scale. The coordinate change is needed only at the insertion `α` (`CoordChangeAlpha0Stmt`). -/
theorem step8PhysExists_of_route1 (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hCal : Step8EventCalibrationStmt.{0}) (hK0 : Step8InsertionTransferK0Stmt) :
    Step8PhysExistsStmt.{0} := by
  intro U V W T Q' Q δ hgeom γ α M hγ0 hγ2 hα hM hE
  obtain ⟨E, F, hPG, hcal, hU⟩ := hCal U V W T Q' Q δ M γ hgeom hγ0 hγ2 hM hE
  refine ⟨E, hPG, fun q hq k => ?_⟩
  exact allModelsAt_all_scales_of_scale_zero hγ0 hγ2 hα hCCα
    (hK0 γ α q δ M U V W T Q' Q hgeom hγ0 hγ2 hα (allModelsAt_zero_scale_zero_of_unit hU (hcal q hq))) k

/-- **Route 1 consumer (universe 0):** `Step8IdentityGivenPinchEventCanonicalStmt.{0}` from the Proposed insertion-`α`
coordinate change `CoordChangeAlpha0Stmt`, the calibration binder `hCal`, and the k = 0 transfer `hK0`. -/
theorem step8Identity_given_pinchEvent_canonical_of_route1
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{0})
    (hCal : Step8EventCalibrationStmt.{0}) (hK0 : Step8InsertionTransferK0Stmt) :
    Step8IdentityGivenPinchEventCanonicalStmt.{0} :=
  step8Identity_given_pinchEvent_canonical_of_physExists (step8PhysExists_of_route1 hCCα hCal hK0)

end HarmonicBalls.FirstPassS11iStep8PhysExists



