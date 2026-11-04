import HarmonicBalls.Proofs.Sec9.AffineObservablesGaussian
import Mathlib.Analysis.Complex.Isometry
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Planar affine changes of variables

The Jacobian of a nonconstant complex affine map is the squared norm of
its linear coefficient.
-/

namespace HarmonicBalls

open MeasureTheory

/-- Integration on the plane under a nonconstant complex affine map. -/
theorem integral_comp_complex_affine (f : ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (∫ z, f (a * z + b)) = (‖a‖ ^ 2)⁻¹ * ∫ z, f z := by
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let u : Circle := ⟨a / ‖a‖, by
    simp [Submonoid.unitSphere, hp.ne']⟩
  have hr := MeasureTheory.integral_comp (rotation u) (fun z : ℂ => f (‖a‖ • z + b))
  have he : ∀ z : ℂ, ‖a‖ • (rotation u) z = a * z := by
    intro z
    change (‖a‖ : ℂ) * ((a / ‖a‖) * z) = a * z
    have hn : (‖a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    field_simp
  simp only [he] at hr
  have hs := Measure.integral_comp_smul volume (fun z : ℂ => f (z + b)) ‖a‖
  rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hp _)),
    ← inv_pow, smul_eq_mul] at hs
  have ht := integral_add_right_eq_self (μ := volume) f b
  rw [ht] at hs
  simpa only [inv_pow] using hr.trans hs

/-- Change of variables for an inverse affine pullback against an arbitrary
weight. No integrability assumption is needed for the Bochner integral. -/
theorem integral_inverse_complex_affine_mul (f g : ℂ → ℝ) {a : ℂ}
    (ha : a ≠ 0) (b : ℂ) :
    (∫ y, f ((y - b) / a) * g y) =
      ‖a‖ ^ 2 * ∫ z, f z * g (a * z + b) := by
  have h := integral_comp_complex_affine (fun y => f ((y - b) / a) * g y) ha b
  have hpoint (z : ℂ) : (a * z + b - b) / a = z := by
    rw [add_sub_cancel_right, mul_comm, mul_div_cancel_right₀ _ ha]
  simp only [hpoint] at h
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  calc
    (∫ y, f ((y - b) / a) * g y) =
        ‖a‖ ^ 2 * ((‖a‖ ^ 2)⁻¹ * ∫ y, f ((y - b) / a) * g y) := by
          rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    _ = ‖a‖ ^ 2 * ∫ z, f z * g (a * z + b) := by rw [← h]

/-- The total mass of an affine pullback has the planar Jacobian factor. -/
theorem integral_comp_inverse_complex_affine (f : ℂ → ℝ) {a : ℂ}
    (ha : a ≠ 0) (b : ℂ) :
    (∫ y, f ((y - b) / a)) = ‖a‖ ^ 2 * ∫ z, f z := by
  simpa only [mul_one] using integral_inverse_complex_affine_mul f (fun _ => 1) ha b

/-- Simultaneous affine substitution in the iterated integral defining a
pairing-pairing covariance. -/
theorem integral_integral_inverse_complex_affine_mul
    (φ ψ : ℂ → ℝ) (K : ℂ → ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (∫ x, φ ((x - b) / a) * ∫ y, ψ ((y - b) / a) * K x y) =
      (‖a‖ ^ 2) ^ 2 * ∫ x, φ x * ∫ y, ψ y * K (a * x + b) (a * y + b) := by
  rw [integral_inverse_complex_affine_mul φ _ ha b]
  have hi (x : ℂ) :
      (∫ y, ψ ((y - b) / a) * K (a * x + b) y) =
      ‖a‖ ^ 2 * ∫ y, ψ y * K (a * x + b) (a * y + b) :=
    integral_inverse_complex_affine_mul ψ _ ha b
  simp_rw [hi]
  have hf : (fun x : ℂ => φ x * (‖a‖ ^ 2 *
      ∫ y, ψ y * K (a * x + b) (a * y + b))) =
      (fun x => ‖a‖ ^ 2 * (φ x * ∫ y, ψ y * K (a * x + b) (a * y + b))) := by
    funext x
    ring
  rw [hf, integral_const_mul]
  ring

/-- Affine substitution in the covariance of two pulled-back pairings. -/
theorem wholePlaneGFFCov_pairings_inverse_complex_affine
    (φ ψ : ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a)))
      (.pairing (fun y => ψ ((y - b) / a))) =
      (‖a‖ ^ 2) ^ 2 * ∫ x, φ x * ∫ y, ψ y * wholePlaneCov (a * x + b) (a * y + b) := by
  exact integral_integral_inverse_complex_affine_mul φ ψ wholePlaneCov ha b

/-- Affine substitution in a pairing-circle covariance. -/
theorem wholePlaneGFFCov_pairing_circle_inverse_complex_affine
    (φ : ℂ → ℝ) {a : ℂ} (ha : a ≠ 0) (b z : ℂ) (r : ℝ) :
    wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a)))
      (.circle (‖a‖ * r) (a * z + b)) =
      ‖a‖ ^ 2 * ∫ x, φ x * Real.circleAverage
        (fun y => wholePlaneCov (a * x + b) (a * y + b)) z r := by
  change (∫ x, φ ((x - b) / a) * Real.circleAverage
    (fun y => wholePlaneCov x y) (a * z + b) (‖a‖ * r)) = _
  rw [integral_inverse_complex_affine_mul φ _ ha b]
  simp_rw [circleAverage_complex_affine]

end HarmonicBalls
