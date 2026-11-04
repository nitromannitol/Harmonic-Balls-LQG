import HarmonicBalls.Steps.Sec11.CompactDiameterSpecialization
import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Proofs.Sec11.NormalizedBaseMetric

/-! # Normalized internal diameters under dilation

The diameter in a dilated compact set and open domain, after dividing by a
positive scale and the circle-average factor, is the internal diameter of the
normalized pullback metric on the original sets. This is a pathwise identity;
no scaling law for the random metric is assumed.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Pulling the metric back by a positive dilation and normalizing it by the
circle-average factor transports the compact internal diameter to fixed sets. -/
theorem scaledCompactInternalDiameter_eq_normalized_pullback
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (ξ : ℝ) (K U : Set ℂ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ω : Ω) :
    scaledCompactInternalDiameter D hcirc ξ K U r (ENNReal.ofReal a) ω =
      ⨆ x ∈ K, ⨆ y ∈ K,
        internalMetric (fun x y => (a * Real.exp (ξ * hcirc ω r 0))⁻¹ *
          D ω (r • x) (r • y)) U x y := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero r hr.ne'
  have he (x : ℂ) : e x = r • x := rfl
  have hp : 0 < a * Real.exp (ξ * hcirc ω r 0) :=
    mul_pos ha (Real.exp_pos _)
  have hdiam := iSup_iSup_internalMetric_comp_homeomorph (D ω) e U K
  simp only [he] at hdiam
  unfold scaledCompactInternalDiameter
  rw [← hdiam]
  simp_rw [internalMetric_const_mul _ (inv_pos.mpr hp)]
  simp_rw [← ENNReal.mul_iSup]
  rw [ENNReal.ofReal_inv_of_pos hp, ENNReal.ofReal_mul ha.le, div_eq_mul_inv, mul_comm]

/-- Under the staged affine-invariance input, the exact-power normalized
compact diameter is the diameter of the metric of the normalized affine field.
The identity holds simultaneously for all points of the fixed compact set. -/
theorem IsWholePlaneGFF.ae_scaledCompactInternalDiameter_eq_affine
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (K U : Set ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P,
      scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω)) hcirc ξ K U r
        (ENNReal.ofReal (r ^ (ξ * lqgQ γ))) ω =
      ⨆ x ∈ K, ⨆ y ∈ K,
        internalMetric (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) U x y := by
  filter_upwards [h.ae_normalized_affine_baseMetric hAff 𝔇 h𝔇 hr] with ω hω
  rw [scaledCompactInternalDiameter_eq_normalized_pullback _ _ _ _ _ hr
    (Real.rpow_pos_of_pos hr _) ω]
  have hfactor : ((r ^ (ξ * lqgQ γ)) * Real.exp (ξ * hcirc ω r 0))⁻¹ =
      Real.exp (-ξ * (hcirc ω r 0 + lqgQ γ * Real.log r)) := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [hfactor]
  have hmetric : (fun x y => Real.exp (-ξ * (hcirc ω r 0 + lqgQ γ * Real.log r)) *
      𝔇 (hC ω) (r • x) (r • y)) =
      𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω) := by
    funext x y
    exact (hω x y).symm
  rw [hmetric]

/-- A uniform first-moment estimate for the affine-field metrics transfers to
normalized diameters at the exponential radii of the puncture argument. -/
theorem IsWholePlaneGFF.scaledCompactInternalDiameter_lintegral_le_of_affine
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (K U : Set ℂ) (s : ℝ) (B : ℝ≥0∞)
    (hmom : ∀ n : ℕ, (∫⁻ ω, ⨆ x ∈ K, ⨆ y ∈ K,
      internalMetric (𝔇 (affinePairing hC hcirc
        (Real.exp (-(s + n)) : ℂ) 0 ω)) U x y ∂P) ≤ B) :
    ∀ n : ℕ, (∫⁻ ω, scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω))
      hcirc ξ K U (Real.exp (-(s + n)))
      (ENNReal.ofReal ((Real.exp (-(s + n))) ^ (ξ * lqgQ γ))) ω ∂P) ≤ B := by
  intro n
  calc
    _ = ∫⁻ ω, ⨆ x ∈ K, ⨆ y ∈ K,
        internalMetric (𝔇 (affinePairing hC hcirc
          (Real.exp (-(s + n)) : ℂ) 0 ω)) U x y ∂P :=
      lintegral_congr_ae (h.ae_scaledCompactInternalDiameter_eq_affine
        hAff 𝔇 h𝔇 K U (Real.exp_pos _))
    _ ≤ B := hmom n

#print axioms IsWholePlaneGFF.scaledCompactInternalDiameter_lintegral_le_of_affine
#print axioms IsWholePlaneGFF.ae_scaledCompactInternalDiameter_eq_affine
#print axioms scaledCompactInternalDiameter_eq_normalized_pullback

end HarmonicBalls
