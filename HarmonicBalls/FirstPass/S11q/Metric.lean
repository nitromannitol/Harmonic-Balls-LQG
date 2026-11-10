import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Steps.Sec11.SingularWeylAffineScaling
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift

/-!
# Dyadic coordinate identities for the LQG metric (Step 12, sections 7.2-7.3)

Notation of Duplantier-Sheffield and Berestycki-Powell: `γ` the LQG parameter, `Q_γ = lqgQ γ`, `ξ` the Weyl
exponent, `𝔇` the metric map `h ↦ D_h`, and `D_h = W_{D_{h^ℂ}}(-α₀ log|·|)` the Weyl scaling (Defs/LQGMetric).
For `R > 0` the dilation is `z ↦ R z`. The constant `c` is the normalization of the paper (31) before the
logarithmic correction: `c_R = c - α₀ log R`.

* `ae_metric_affinePullback_background_shift` (paper eq. (37), background level): `𝔇` of the dilated background
  shifted by the random constant `Q_γ log R - c` equals `e^{-ξ c}` times `𝔇(hC)(R·, R·)`. It uses only clauses III
  (constant Weyl scaling, `IsWholePlaneGFF.ae_metric_background_add_random_constant`) and IV (coordinate change,
  `SatisfiesLQGMetricAxioms.coordChange`).
* `ae_weylScaling_affinePullback_background` (paper eq. (33)): the Weyl scaling of that metric with the singular
  weight `-α₀ log|·|` equals `e^{-ξ c_R} · W_{D_{hC}}(-α₀ log|·|)(R u, R v)`, `c_R = c - α₀ log R` (paper (31)).
  The value at `0` (section 7.3) is handled by the cited Sec11 lemma, through the deterministic fact that a
  length-parametrized path spends zero Lebesgue time at `0` (`IsEuclideanLengthMetric.ae_ne_of_lengthParametrized`).
  Here the Lean convention `log 0 = 0` is harmless because the weight at `0` is never evaluated on a set of
  positive time.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Adding the zero function to a pairing functional does nothing. -/
lemma addFunPairing_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

/-- Two constant shifts of a pairing functional add. -/
lemma addFunPairing_const_const (T : (ℂ → ℝ) → ℝ) (a b : ℝ) :
    addFunPairing (addFunPairing T (fun _ => a)) (fun _ => b) = addFunPairing T (fun _ => a + b) := by
  funext φ
  simp only [addFunPairing, integral_const_mul]
  ring

/-- Change of variables `x ↦ x / r` on `ℂ` for `r > 0`: the Lebesgue integral picks up `r ^ 2`. -/
lemma integral_div_ofReal_eq (φ : ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ x : ℂ, φ (x / (r : ℂ)) = r ^ 2 * ∫ x : ℂ, φ x := by
  have h1 : ∀ x : ℂ, x / (r : ℂ) = (r⁻¹ : ℝ) • x := fun x => by
    rw [Complex.real_smul]
    push_cast
    rw [div_eq_inv_mul]
  simp_rw [h1]
  have hab : |(r⁻¹ ^ 2)⁻¹| = r ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    simp
  rw [Measure.integral_comp_smul volume φ r⁻¹, Complex.finrank_real_complex, smul_eq_mul, hab]

/-- The affine pullback `T ↦ T(r ·)` (at `z = 0`) commutes with a constant shift: `(T + c)(r ·) = T(r ·) + c`. -/
lemma affinePullbackPairing_addFunPairing_const (T : (ℂ → ℝ) → ℝ) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    affinePullbackPairing (addFunPairing T (fun _ => c)) r 0 =
      addFunPairing (affinePullbackPairing T r 0) (fun _ => c) := by
  funext φ
  have hI : ∫ x : ℂ, c * φ ((x - 0) / (r : ℂ)) = r ^ 2 * ∫ x : ℂ, c * φ x := by
    simp only [sub_zero]
    rw [integral_const_mul, integral_const_mul, integral_div_ofReal_eq φ hr]
    ring
  simp only [affinePullbackPairing, addFunPairing, sub_zero] at hI ⊢
  have hr2 : r ^ 2 ≠ 0 := by positivity
  rw [hI, mul_add, ← mul_assoc, inv_mul_cancel₀ hr2, one_mul]

/-- Paper eq. (37) at the background level. For a whole-plane GFF background `hC` and a random real constant `c`,
almost surely for all `u v`, the metric of the dilated background `hC(R ·) + Q_γ log R - c` is
`e^{-ξ c} D_{hC}(R u, R v)`. -/
theorem ae_metric_affinePullback_background_shift
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {R : ℝ} (hR : 0 < R) (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R - c ω)) u v =
        Real.exp (-(ξ * c ω)) * 𝔇 (hC ω) (R * u) (R * v) := by
  have hIV := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω _ => -c ω) hG
    (fun _ => continuous_const) (fun _ => hc.neg)).coordChange R hR 0
  have hIII := IsWholePlaneGFF.ae_metric_background_add_random_constant hG 𝔇 h𝔇
    (fun _ => 0) continuous_const (fun ω => -c ω) hc.neg
  filter_upwards [hIV, hIII] with ω hω1 hω2
  simp only [add_zero, zero_add, addFunPairing_zero] at hω1 hω2
  intro u v
  have h1 := hω1 u v
  have h2 := hω2 (R * u) (R * v)
  rw [affinePullbackPairing_addFunPairing_const _ _ hR, addFunPairing_const_const] at h1
  have hf : (fun _ : ℂ => -c ω + lqgQ γ * Real.log R) = fun _ => lqgQ γ * Real.log R - c ω := by
    funext _
    ring
  rw [hf, h2] at h1
  rw [← h1, mul_neg]

/-- The Lebesgue-a.e. Euclidean length property of the background metric `D_{hC}`, from clause I. -/
lemma ae_isEuclideanLengthMetric_background
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
  have h0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)
  filter_upwards [h0.ae_isEuclideanLengthMetric] with ω hω
  simpa only [addFunPairing_zero] using hω


/-- Section 7.3 (value at `0`): a length-parametrized path spends zero Lebesgue time at the point `0`, so the
Lean value `ℝ`-log at `0` (`Real.log 0 = 0`) never matters in the Weyl integrals. -/
lemma ae_time_ne_zero_of_lengthParametrized {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized D p T) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ 0 :=
  hD.ae_ne_of_lengthParametrized hp 0

/-- Paper eq. (33) at the Weyl-scaling level. With the background metric of `h^(R)` equal to `hC(R ·) + Q_γ log R - c`
(paper (34)), almost surely for all `u v`,
`W_{D_{h^(R)}}(-α₀ log|·|)(u, v) = e^{-ξ c_R} · W_{D_{hC}}(-α₀ log|·|)(R u, R v)` with `c_R = c - α₀ log R` (paper (31)).
The constant is `e^{-ξ c} · e^{ξ α₀ log R}` by the Sec11 identity `weylScaling_log_const_mul_comp_real_smul`. -/
theorem ae_weylScaling_affinePullback_background
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {R : ℝ} (hR : 0 < R) (c : Ω → ℝ) (hc : Measurable c) (α₀ : ℝ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R - c ω)))
          ξ (fun x => -α₀ * Real.log ‖x‖) u v =
        ENNReal.ofReal (Real.exp (-(ξ * (c ω - α₀ * Real.log R)))) *
          weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) (R * u) (R * v) := by
  filter_upwards [ae_metric_affinePullback_background_shift hG 𝔇 h𝔇 hR c hc,
    ae_isEuclideanLengthMetric_background hG 𝔇 h𝔇] with ω hω hDω
  intro u v
  have hfun : 𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R - c ω)) =
      fun x y => Real.exp (-(ξ * c ω)) * 𝔇 (hC ω) (R * x) (R * y) :=
    funext fun x => funext fun y => hω x y
  have hS := IsEuclideanLengthMetric.weylScaling_log_const_mul_comp_real_smul hDω ξ α₀ hR
    (Real.exp_pos (-(ξ * c ω))) u v
  simp only [Complex.real_smul] at hS
  rw [hfun, hS]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end HarmonicBalls
