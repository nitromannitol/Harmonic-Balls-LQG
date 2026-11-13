import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11i.Step8Frequency
import HarmonicBalls.FirstPass.S11i.Corrected11_13
import HarmonicBalls.FirstPass.S11i.Step8Event
import HarmonicBalls.FirstPass.S11i.Step8ZoomFrequency

/-!
# Step 8 physical frequency: the zoom of an insertion-`α₀` model

Corrected paper, Step 8 of `lemma:mu_h-pinch-bad` (lines 3848-3930), dilation paragraph. The zoom route of
`hzoom_all_of_unit_models` / `hphys_of_zoom_const_family`, written for the insertion `α₀` (the existing chain is for
`α₀ = 0` only):
* zoom at `2^k`: the normalized model `(normField 2^k, normCirc 2^k, normMeasureAlpha, Dk)` is an insertion-`α₀` model.
  The measure part is `isLQGMeasureOfField_normMeasure_alpha` (proved here, from `LQGMeasureCoordChange` at `α₀`, a
  Proposed input, Fact 2.1 IV, pending source-check). The metric part is `ZoomMetricNormAlpha0Stmt`.
* transfer to the physical frequency: `hphys_of_zoom_const_family` (existing, proved).

The identification `F = E` is definitional at the level of the frequency (`step8Frequency_eq_localModConst`). The
physical frequency for a chosen pinch event is assembled in `S11i/Step8PhysExists.lean`.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8PhysReduction

open MeasureTheory Filter Topology Set Metric FirstPassS11i HarmonicBalls
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8Zoom
open scoped ENNReal

/-! ### Named binders (exact types) -/

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

/-- **Input (Proposed, pending source-check): coordinate change of the LQG measure at `α₀`** (Fact 2.1 IV,
`LQGMeasureCoordChange`, `Proposed/LQG.lean:116`), for every whole-plane model. -/
def CoordChangeAlpha0Stmt.{v} : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc

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

end HarmonicBalls.FirstPassS11iStep8PhysReduction

