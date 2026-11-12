import HarmonicBalls.FirstPass.Phase2.Step8TransferK0FixedMetric
import HarmonicBalls.FirstPass.Phase2.Step8PerModelWholePlane
import HarmonicBalls.FirstPass.Phase2.CoordChangeHolds

/-!
# Step 8 of Lemma 11.13: every dyadic scale and the whole plane, for one fixed LQG metric

Fix an LQG metric `𝔇` (`IsLQGMetric γ ξ 𝔇`). A whole-plane insertion-`α` model is *a model of `𝔇`* if its metric is,
almost surely, the Weyl scaling of `𝔇` at its field with the `α`-log singularity. The zoom of such a model at scale `2^k`
(`zoomMetric`), renormalized by the circle average `h_{2^k}(0)`, is again a model of `𝔇` up to a positive constant
(`zoom_metric_alpha_identity`): the coordinate change of the LQG metric keeps `𝔇`. So the unit-scale certificate
frequency of all models of `𝔇` gives the frequency at every scale `2^k` (proof of `allModelsAt_all_scales_of_scale_zero`
with the models restricted to those of `𝔇`), and hence, since the balls `B(0, 2^k)` exhaust `ℂ` and the radii
`2^k 2⁻ⁿ = 2^{-(n-k)}` only shift the window index by `k`, the frequency at the radii `2⁻ⁿ` about `μ`-almost every point
of the plane (paper, `eq:dyadic-frequency`).

## Main results
* `zoomMetricNormAlpha_fixedMetric`: the zoom of a model of `𝔇` is a positive constant times a model of `𝔇` for the
  renormalized field `normField 2^k`.
* `physicalAt_all_scales_fixedMetric`: unit-scale frequency for all models of `𝔇` gives every scale `2^k`.
* `tendsto_window_frequency_unshift`, `ae_tendsto_wholePlane_of_physicalAt`: all scales give the whole plane.
* `ae_tendsto_wholePlane_fixedMetric_of_seed`: from the fixed-metric seed of Lemma 11.12 and a common probability `q`
  of its coding event, every insertion-`α` model of `𝔇` has the whole-plane window frequency `q` at the radii `2⁻ⁿ`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit HarmonicBalls.FirstPassS11iHzoom

namespace HarmonicBalls.FirstPassPhase2Step8AllScalesFixedMetric

open HarmonicBalls HarmonicBalls.S11c FirstPassS11i FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11iStep8Zoom

/-- **Zoom of a model of a fixed LQG metric.** If `D` is almost surely the Weyl scaling of `𝔇 (h^ℂ)` by `-α log|·|`,
then for every `k` there is `Dk`, almost surely the Weyl scaling of `𝔇` at the renormalized field `normField 2^k` by
`-α log|·|`, such that almost surely the zoom of `D` at scale `2^k` is a positive constant times `Dk`. The constant is
`e^{ξ C}` with `C = h_{2^k}(0) + (Q_γ - α) log 2^k`. Proof of `zoomMetricNormAlpha_of_isLQGMetricOfField`, which
already uses one fixed `𝔇`. -/
theorem zoomMetricNormAlpha_fixedMetric {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ α : ℝ}
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    (hDae : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v) (k : ℕ) :
    ∃ Dk : Ω₀ → ℂ → ℂ → ℝ,
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ Dk ω u v ∧ ENNReal.ofReal (Dk ω u v) =
        weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ (fun x => -α * Real.log ‖x‖) u v) ∧
      ∀ᵐ ω ∂P, ∃ B : ℝ, 0 < B ∧ ∀ x y, zoomMetric (D ω) k x y = B * Dk ω x y := by
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hid := FirstPassS11iZoomMetricAlpha0.zoom_metric_alpha_identity hM hG hDae hR
  refine ⟨fun ω x y => (weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
      (fun x => -α * Real.log ‖x‖) x y).toReal, ?_, ?_⟩
  · filter_upwards [hid] with ω hω
    intro u v
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) u v ≠ ⊤ := by
      intro htop
      have h := hω u v
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin⟩
  · filter_upwards [hid, hDae] with ω hω hDω
    refine ⟨Real.exp (ξ * (hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k))),
      Real.exp_pos _, fun x y => ?_⟩
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) x y ≠ ⊤ := by
      intro htop
      have h := hω x y
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    have h := hω x y
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
    simp only [zoomMetric, one_mul]
    exact (ENNReal.ofReal_eq_ofReal_iff (hDω _ _).1
      (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)).mp h

/-- **Zoomed unit-ball frequencies of a model of a fixed LQG metric.** The statement of `hzoom_alpha_all_of_scale_zero`
for a model of `𝔇`, from the scale-`0` frequency `h0` of all insertion-`α` models of `𝔇`: the renormalized model at
scale `2^k` is again a model of `𝔇` (`zoomMetricNormAlpha_fixedMetric`). -/
theorem hzoom_alpha_all_of_scale_zero_fixedMetric {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ α q δ M : ℝ} {U V W T Q' Q : Set ℂ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v) →
        FirstPassS11iInsertionTransfer.PhysicalAt P q U V W T Q' Q δ M 0 μ D) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  intro k
  obtain ⟨Dk, hDk, hscale⟩ := zoomMetricNormAlpha_fixedMetric hG hM hD k
  have hR : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hGk := isWholePlaneGFF_normalized hG hR
  have hμk := HarmonicBalls.FirstPassS11iStep8PhysReduction.isLQGMeasureOfField_normMeasureAlpha
    hγ0 hγ2 hα hG hμ (HarmonicBalls.coordChangeAlpha0Stmt_holds.{0} γ α Ω P hC hcirc) k
  have hU := h0 Ω P (normField ((2 : ℝ) ^ k) hC hcirc) (normCirc ((2 : ℝ) ^ k) hcirc)
    (HarmonicBalls.FirstPassS11iStep8PhysReduction.normMeasureAlpha γ α μ hcirc k) Dk hGk hμk hDk
  unfold FirstPassS11iInsertionTransfer.PhysicalAt at hU
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

/-- **Every dyadic scale for one fixed LQG metric.** If every insertion-`α` model of `𝔇` has the certificate frequency
`q` at scale `2⁰`, then every insertion-`α` model of `𝔇` has it at every scale `2^k`. -/
theorem physicalAt_all_scales_fixedMetric {γ ξ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    (h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v) →
        FirstPassS11iInsertionTransfer.PhysicalAt P q U V W T Q' Q δ M 0 μ D) (k : ℕ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v) →
        FirstPassS11iInsertionTransfer.PhysicalAt P q U V W T Q' Q δ M k μ D := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  unfold FirstPassS11iInsertionTransfer.PhysicalAt
  exact (HarmonicBalls.FirstPassS11iStep8Transfer.hphys_of_zoom_const_family P U V W T Q' Q δ M q μ D
    (hzoom_alpha_all_of_scale_zero_fixedMetric hγ0 hγ2 hα hM hG hμ hD h0)) k

/-- **Inverse index shift of the window frequency.** If the window frequency of the events `A (n - k)`,
`n ∈ [N + 1, 2N]`, tends to `q`, so does the window frequency of the events `A n`. -/
lemma tendsto_window_frequency_unshift (A : ℕ → Prop) (k : ℕ) {q : ℝ}
    (h : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  have hbound : ∀ N : ℕ, |({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ) -
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ)| ≤ k := by
    intro N
    have h1 : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℕ) : ℝ) + k := by
      exact_mod_cast ncard_window_shift_le A k N
    have h2 : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℕ) : ℝ) + k := by
      exact_mod_cast ncard_window_unshift_le A k N
    rw [abs_le]
    constructor <;> linarith
  have hdiff : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ) / (N : ℝ) -
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
    rw [Real.norm_eq_abs, ← sub_div, abs_div, Nat.abs_cast]
    gcongr
    exact hbound N
  have hsum := h.add hdiff
  rw [add_zero] at hsum
  exact hsum.congr fun N => by ring

/-- **The whole plane from every dyadic scale.** If a model has the certificate frequency `q` at every scale `2^k`
(on `B(0, 2^k)`, radii `2^k 2⁻ⁿ`), then almost surely, for `μ`-almost every `z ∈ ℂ`, the window frequency of the
certificate events at the radii `2⁻ⁿ` about `z` tends to `q`: the balls `B(0, 2^k)` exhaust `ℂ`, and
`2^k 2⁻ⁿ = 2^{-(n-k)}` shifts the window index by `k`. -/
theorem ae_tendsto_wholePlane_of_physicalAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : ∀ k : ℕ, FirstPassS11iInsertionTransfer.PhysicalAt P q U V W T Q' Q δ M k μ D) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) z}.ncard
          : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  have h' : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
    intro k
    have hk := h k
    unfold FirstPassS11iInsertionTransfer.PhysicalAt at hk
    exact hk
  filter_upwards [ae_all_iff.2 h'] with ω hω
  filter_upwards [ae_all_iff.2 hω] with z hzk
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ (by norm_num : (1 : ℝ) < 2)
  have hk' : z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) := mem_ball_zero_iff.2 hk
  refine tendsto_window_frequency_unshift (fun m => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ)
    U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ m) z) k ((hzk k hk').congr' ?_)
  filter_upwards [eventually_ge_atTop k] with N hN
  have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ)
      U V W T Q' Q δ M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ)
      U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ (n - k)) z} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun h1 => and_congr_right fun _ => ?_
    rw [two_pow_mul_inv_two_pow_eq (by omega : k ≤ n)]
  exact congrArg (fun s : Set ℕ => ((s.ncard : ℕ) : ℝ) / (N : ℝ)) hset

open HarmonicBalls.FirstPassPhase2Step8TransferK0FixedMetric in
/-- **Whole-plane certificate frequency of every insertion-`α` model of one fixed LQG metric, from the seed of
Lemma 11.12.** Let `𝔇` be an LQG metric, `E` a measurable coding event satisfying the seed `hEq` for `𝔇`, and `q` a
common probability of `E`. Then for `α < Q_γ`, in every whole-plane insertion-`α` model whose metric is, almost surely,
the Weyl scaling of `𝔇` at its field with the `α`-log singularity, almost surely, for `μ`-almost every `z ∈ ℂ`, the
window frequency of the certificate events at the radii `2⁻ⁿ` about `z` tends to `q` (paper, `eq:dyadic-frequency`).
Remaining inputs: `hR`, `hfr` and `hAx`. -/
theorem ae_tendsto_wholePlane_fixedMetric_of_seed {γ α δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    {q : ℝ} (hq : CommonProb.{0} γ E q) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
          Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) z}.ncard
              : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact ae_tendsto_wholePlane_of_physicalAt fun k =>
    physicalAt_all_scales_fixedMetric hγ0 hγ2 hα h𝔇
      (physicalAt_insertion_fixedMetric_of_seed hγ0 hγ2 hα hgeo hR hfr hAx h𝔇 hE hEq hq) k
      Ω P hC hcirc μ D hG hμ hD

end HarmonicBalls.FirstPassPhase2Step8AllScalesFixedMetric
