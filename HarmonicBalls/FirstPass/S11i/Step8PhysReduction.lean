import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11i.Step8Frequency
import HarmonicBalls.FirstPass.S11i.Step8IdentityAssembly

/-!
# Step 8 physical frequency `hPhys`: reduction to the unit-scale statement (fp-S11-13-hPhys-reduction, owner n3)

`Step8PhysStmt` is the binder `hPhys` of `step8Identity_given_pinchEvent_canonical_of_phys`
(`S11i/Step8IdentityAssembly.lean`): for every insertion-`α₀` model and every `k`, almost surely the physical window
frequency on `B_{2^k}(0)` tends to `q`. Corrected paper, Step 8 of `lemma:mu_h-pinch-bad` (lines 3848-3930), dilation
paragraph.

Reduction (no new mathematics). The zoom route of `hzoom_all_of_unit_models` / `hphys_of_zoom_const_family`, written for
the insertion `α₀` (the existing chain is for `α₀ = 0` only):
* zoom at `2^k` (ii): the normalized model `(normField 2^k, normCirc 2^k, normMeasureAlpha, Dk)` is an insertion-`α₀` model.
  The measure part is `isLQGMeasureOfField_normMeasure_alpha` (proved here, from `LQGMeasureCoordChange` at `α₀`, a
  Proposed input, Fact 2.1 IV, pending source-check). The metric part is `ZoomMetricNormAlpha0Stmt` (NAMED BINDER, MISSING).
* unit scale (i): `Step8UnitScaleAlpha0Stmt` (NAMED BINDER, MISSING): the unit-ball frequency at `q` for every
  insertion-`α₀` model.
* transfer to the physical frequency: `hphys_of_zoom_const_family` (existing, proved).

The identification `F = E` is definitional at the level of the frequency (`step8Frequency_eq_localModConst`), but NOT at
the level of the decoded certificate event; that identity is inside `Step8UnitScaleAlpha0Stmt` (see its docstring).
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8PhysReduction

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8Zoom
open scoped ENNReal

/-! ### Named binders (MISSING inputs, exact types) -/

/-- **MISSING input (route (i)): unit-scale statement for every insertion-`α₀` model.** Let `E` be the premise event of
`PinchEventGammaCanonicalStmt` at `γ`, and let `q` satisfy the `(A)` property: `P{localModConstField γ hC (ball 0 7) ∈ E}`
has value `q` in every whole-plane model. Then every insertion-`α₀` LQG model `(μ, D)` (`IsLQGMeasureOfField P γ α₀`,
`IsLQGMetricOfField P γ (lqgXi γ) α₀`) has the unit-ball frequency `q` (`UnitBallFrequencyStmt`, radii `2⁻ⁿ`,
Ostar `pinchOmegaGeom W Q δ₀`, `η = δ₀`). The insertion-`0` analogue is `UnitBallFrequencyModelsStmt`
(`S11i/HzoomScale.lean:124`, n4).

Not supplied by the premise: the decoded certificate event of `ae_unitScale_of_decoded_ball` (`S11i/Step8Decoded.lean:43`,
`hFdef`) must equal `E`, i.e. `∀ L, CertificateEvent (Dμ L) (Dd L) Ostar U' V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ E`
for the decoded models. `PinchEventGammaStmt` (`S11i/Assembly13.lean:120`) gives only measurability, positivity, and
`E ⇒ pinchPointEvent` a.s. (one-sided). -/
def Step8UnitScaleAlpha0Stmt.{v} : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
    ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
    ∀ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{v} U T Q' Q γ M E →
    ∀ q : ℝ, (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) →
    ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
      UnitBallFrequencyStmt P q U V W T Q' Q δ₀ M μ D

/-- The zoom of the LQG metric at scale `2^k` is, up to a positive constant, the metric of the normalized field, for the
insertion `α₀` (`IsLQGMetricOfField`). At `α₀ = 0` this is `ZoomMetricNormStmt` (`S11i/HzoomScale.lean:132`, proved). -/
def ZoomMetricNormAlphaFor {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ Dk : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ α₀ (normField ((2 : ℝ) ^ k) hC hcirc) Dk ∧
    ∀ᵐ ω ∂P, ∃ B : ℝ, 0 < B ∧ ∀ x y, zoomMetric (D ω) k x y = B * Dk ω x y

/-- **MISSING input (route (ii), metric part): zoom of the insertion-`α₀` LQG metric.** For every whole-plane model
`(Ω, P, hC, hcirc)` and every LQG metric `D` of `h^ℂ - α₀ log |·|`, `ZoomMetricNormAlphaFor` holds. Source: Fact 2.2 III-IV
(paper, Weyl scaling and coordinate change of the metric, lines 432-457) for the insertion `α₀`. In Lean it needs the
dilation of `weylScaling` along paths (`LQGMetric.lean:107`) and the constant-factor rule `weylScaling (B • D) = B • weylScaling D`,
neither in the repository. -/
def ZoomMetricNormAlpha0Stmt.{v} : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D → ZoomMetricNormAlphaFor P γ ξ α₀ hC hcirc D

/-- **Input (Proposed, pending operator source-check): coordinate change of the LQG measure at `α₀`** (Fact 2.1 IV,
`LQGMeasureCoordChange`, `Proposed/LQG.lean:116`), for every whole-plane model. -/
def CoordChangeAlpha0Stmt.{v} : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc

/-- The binder `hPhys` of `step8Identity_given_pinchEvent_canonical_of_phys` (`S11i/Step8IdentityAssembly.lean`), named. -/
def Step8PhysStmt.{v} : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
    ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
    ∀ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{v} U T Q' Q γ M E →
    ∀ q : ℝ, (∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) →
    ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
      ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀) U V W T Q' Q δ₀ M
            ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)

/-! ### (iii) The identification `F = E` at the level of the frequency -/

/-- **`F = E` at the frequency level (definitional).** The Step-8 frequency of the set `E` is the `(A)` probability of
`E`: `ballRestrictPairing 7 (alphaCanon γ hC ω) = localModConstField γ hC (ball 0 7) ω` (`S11i/CertificateCanonical.lean:27`,
proved by `funext; rfl`). -/
theorem step8Frequency_eq_localModConst {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) :
    HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency P γ hC E =
      (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal := by
  unfold HarmonicBalls.FirstPassS11iStep8Frequency.step8Frequency
  simp only [HarmonicBalls.S11iCert.ballRestrict_alphaCanon_eq]

/-! ### (ii) The zoom of an insertion-`α₀` model at scale `2^k` -/

/-- Circle averages of the affine renormalization at `R > 0` (insertion `α₀`): the `α₀ log |·|` term contributes
`α₀ log R`, which is absorbed in the constant of `normMeasureAlpha`. -/
theorem fieldCircleAverage_normCirc_eq {Ω : Type*} (α₀ R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (z : ℂ) :
    fieldCircleAverage α₀ (normCirc R hcirc ω) ε z =
      fieldCircleAverage α₀ (hcirc ω) (R * ε) ((R : ℂ) * z) + α₀ * Real.log R - hcirc ω R 0 := by
  have hn : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hsmul : Real.circleAverage (fun x => Real.log ‖x‖) ((R : ℂ) * z) (R * ε) =
      Real.log R + Real.circleAverage (fun x => Real.log ‖x‖) z ε := by
    rw [circleAverage_log_norm (mul_pos hR hε), circleAverage_log_norm hε, norm_mul, hn,
      ← mul_max_of_nonneg _ _ hR.le, Real.log_mul hR.ne'
        (lt_of_lt_of_le hε (le_max_left _ _)).ne']
  simp only [fieldCircleAverage, normCirc, hn, add_zero]
  rw [hsmul]
  ring

/-- Congruence of `IsLQGLimit` on the positive scales (only `hε ε` for `ε > 0` enters the dyadic approximations). -/
theorem isLQGLimit_congr_pos {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, hε ε z = hε' ε z) (hl : IsLQGLimit γ hε m) : IsLQGLimit γ hε' m where
  isLocallyFiniteMeasure := hl.isLocallyFiniteMeasure
  tendsto_integral := by
    intro f hf hc
    have hA : ∀ k : ℕ, lqgApprox γ hε' (dyadicScale k) = lqgApprox γ hε (dyadicScale k) := by
      intro k
      simp only [lqgApprox, h _ (dyadicScale_pos k)]
    simp only [hA]
    exact hl.tendsto_integral f hf hc

/-- The normalized insertion-`α₀` measure at scale `2^k`: `e^{-γ C_k^{α₀}} · zoomMeasure (μ ω) k` with
`C_k^{α₀} = hcirc R 0 + (Q - α₀) log R`, `R = 2^k`. At `α₀ = 0` this is `normMeasure` (`S11i/HzoomScale.lean:83`). -/
noncomputable def normMeasureAlpha {Ω : Type*} (γ α₀ : ℝ) (μ : Ω → Measure ℂ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (ω : Ω) : Measure ℂ :=
  ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α₀) * Real.log ((2 : ℝ) ^ k))))) •
    zoomMeasure (μ ω) k

/-- **Normalized insertion-`α₀` measure is an LQG measure.** The insertion-`α₀` analogue of
`isLQGMeasureOfField_normMeasure` (`S11i/HzoomScale.lean:89`), input `LQGMeasureCoordChange` at `α₀`. -/
theorem isLQGMeasureOfField_normMeasureAlpha {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc) (k : ℕ) :
    IsLQGMeasureOfField P γ α₀ (normCirc ((2 : ℝ) ^ k) hcirc) (normMeasureAlpha γ α₀ μ hcirc k) := by
  have hae := hCC hG hγ0 hγ2 hα μ hμ
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  unfold IsLQGMeasureOfField IsLQGMeasure
  filter_upwards [hae] with ω hω
  have hne : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have h := hω _ hne 0
  have hnorm : ‖(((2 : ℝ) ^ k : ℝ) : ℂ)‖ = (2 : ℝ) ^ k := by
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have key := isLQGLimit_add_const (γ := γ)
    (c := -(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α₀) * Real.log ((2 : ℝ) ^ k))) h
  have hm : normMeasureAlpha γ α₀ μ hcirc k ω =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α₀) * Real.log ((2 : ℝ) ^ k))))) •
        ((μ ω).map fun x => (x - 0) / (((2 : ℝ) ^ k : ℝ) : ℂ)) := by
    simp only [normMeasureAlpha, zoomMeasure, ENNReal.ofReal_one, one_smul, sub_zero]
  rw [hm]
  refine isLQGLimit_congr_pos (fun ε hε0 z => ?_) key
  simp only [hnorm, add_zero]
  rw [fieldCircleAverage_normCirc_eq α₀ ((2 : ℝ) ^ k) ε hR hε0 hcirc ω z]
  ring

/-- **Every `hzoom(k)` for the insertion-`α₀` model.** Same proof as `hzoom_all_of_unit_models`
(`S11i/HzoomScale.lean:141`), with the normalized measure `normMeasureAlpha` and the unit-scale input for every
insertion-`α₀` model (`hunit`, at the fixed `P`). -/
theorem hzoom_all_of_unit_models_alpha {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {D : Ω → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hMetric : ZoomMetricNormAlphaFor P γ ξ α₀ hC hcirc D)
    (hunit : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ α₀ hcirc' μ' → IsLQGMetricOfField P γ ξ α₀ hC' D' →
        UnitBallFrequencyStmt P q U V W T Q' Q δ M μ' D') :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  intro k
  obtain ⟨Dk, hDk, hscale⟩ := hMetric k
  have hR : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hGk := isWholePlaneGFF_normalized hG hR
  have hμk := isLQGMeasureOfField_normMeasureAlpha hγ0 hγ2 hα hG hμ hCC k
  have hU := hunit (normField ((2 : ℝ) ^ k) hC hcirc) (normCirc ((2 : ℝ) ^ k) hcirc)
    (normMeasureAlpha γ α₀ μ hcirc k) Dk hGk hμk hDk
  filter_upwards [hU, hscale] with ω hω hsc
  obtain ⟨B, hB, hBeq⟩ := hsc
  have hmet : (fun x y => B⁻¹ * zoomMetric (D ω) k x y) = Dk ω := by
    funext x y
    rw [hBeq x y, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]
  refine ⟨Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α₀) * Real.log ((2 : ℝ) ^ k)))), B⁻¹,
    Real.exp_pos _, inv_pos.mpr hB, ?_⟩
  have hmeas : ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 +
      (lqgQ γ - α₀) * Real.log ((2 : ℝ) ^ k))))) • zoomMeasure (μ ω) k =
        normMeasureAlpha γ α₀ μ hcirc k ω := rfl
  rw [hmeas, hmet]
  exact hω

/-! ### The reduction of `hPhys` -/

/-- **Reduction of `hPhys` to the unit-scale statement.** From the unit-scale binder `hUnit` (route (i)), the coordinate
change at `α₀` (`hCC`, Proposed) and the metric zoom `hMet` (route (ii), MISSING), the physical window frequency
`Step8PhysStmt` follows: zoom at each `2^k` (`hzoom_all_of_unit_models_alpha`), then `hphys_of_zoom_const_family`. -/
theorem hPhys_of_unit_models.{v} (hUnit : Step8UnitScaleAlpha0Stmt.{v}) (hCC : CoordChangeAlpha0Stmt.{v})
    (hMet : ZoomMetricNormAlpha0Stmt.{v}) : Step8PhysStmt.{v} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM E hPG q hq Ω _ P hC hcirc μ D hG hμ hD
  exact HarmonicBalls.FirstPassS11iStep8Transfer.hphys_of_zoom_const_family P U V W T Q' Q δ₀ M q μ D
    (hzoom_all_of_unit_models_alpha hγ0 hγ2 hα hG hμ (hCC γ α₀ Ω P hC hcirc)
      (hMet γ (lqgXi γ) α₀ Ω P hC hcirc D hG hD)
      (fun hC' hcirc' μ' D' h1 h2 h3 =>
        hUnit U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM E hPG q hq Ω P hC' hcirc' μ' D' h1 h2 h3))

/-- **Step 8 identification (Lemma 11.13) from the unit-scale statement.** `hPhys_of_unit_models` fed into
`step8Identity_given_pinchEvent_canonical_of_phys`. Missing inputs: `hUnit` (route (i)) and `hMet` (route (ii)). -/
theorem step8Identity_of_unit_scale.{v} (hUnit : Step8UnitScaleAlpha0Stmt.{v}) (hCC : CoordChangeAlpha0Stmt.{v})
    (hMet : ZoomMetricNormAlpha0Stmt.{v}) : Step8IdentityGivenPinchEventCanonicalStmt.{v} :=
  HarmonicBalls.FirstPassS11iStep8IdentityAssembly.step8Identity_given_pinchEvent_canonical_of_phys
    (hPhys_of_unit_models hUnit hCC hMet)

end HarmonicBalls.FirstPassS11iStep8PhysReduction

#print axioms HarmonicBalls.FirstPassS11iStep8PhysReduction.hPhys_of_unit_models
#print axioms HarmonicBalls.FirstPassS11iStep8PhysReduction.step8Identity_of_unit_scale
#print axioms HarmonicBalls.FirstPassS11iStep8PhysReduction.step8Frequency_eq_localModConst
