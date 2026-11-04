import HarmonicBalls.Proofs.Sec9.ComplexAffineIntegral

/-! # Affine transformation of the pairing-circle covariance

Circle averaging removes the logarithmic point singularity before the
remaining planar integration.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- Affine transformation of the circle-averaged whole-plane kernel. -/
theorem circleAverage_wholePlaneCov_complex_affine {a : ℂ} (ha : a ≠ 0)
    (b z x : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun y => wholePlaneCov (a * x + b) y)
        (a * z + b) (‖a‖ * r) =
      Real.circleAverage (fun y => wholePlaneCov x y) z r +
        (wholePlaneNormalization (a * x + b) - wholePlaneNormalization x) +
        (Real.circleAverage wholePlaneNormalization (a * z + b) (‖a‖ * r) -
          Real.circleAverage wholePlaneNormalization z r) - Real.log ‖a‖ := by
  have hp : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hd : (a * z + b) - (a * x + b) = a * (z - x) := by ring
  rw [circleAverage_wholePlaneCov_eq (mul_pos hp hr), circleAverage_wholePlaneCov_eq hr,
    hd, norm_mul, ← mul_max_of_nonneg _ _ hp.le,
    Real.log_mul hp.ne' (ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))]
  ring

/-- The mixed covariance changes by the two one-point normalization terms
and the logarithm of the scale. -/
theorem wholePlaneGFFCov_pairing_circle_complex_affine
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {a : ℂ} (ha : a ≠ 0) (b z : ℂ) {r : ℝ} (hr : 0 < r) :
    wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a)))
      (.circle (‖a‖ * r) (a * z + b)) =
      ‖a‖ ^ 2 * (wholePlaneGFFCov (.pairing φ) (.circle r z) +
        (∫ x, φ x * (wholePlaneNormalization (a * x + b) - wholePlaneNormalization x)) +
        (∫ x, φ x) * (Real.circleAverage wholePlaneNormalization (a * z + b) (‖a‖ * r) -
          Real.circleAverage wholePlaneNormalization z r - Real.log ‖a‖)) := by
  let A : ℂ → ℝ := fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r
  let D : ℂ → ℝ := fun x => wholePlaneNormalization (a * x + b) - wholePlaneNormalization x
  let c : ℝ := Real.circleAverage wholePlaneNormalization (a * z + b) (‖a‖ * r) -
    Real.circleAverage wholePlaneNormalization z r - Real.log ‖a‖
  have hA : Continuous A := continuous_circleAverage_wholePlaneCov hr z
  have hD : Continuous D := (continuous_wholePlaneNormalization.comp (by fun_prop)).sub
    continuous_wholePlaneNormalization
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hAi : Integrable (fun x => φ x * A x) :=
    (hφ.mul hA).integrable_of_hasCompactSupport hφc.mul_right
  have hDi : Integrable (fun x => φ x * D x) :=
    (hφ.mul hD).integrable_of_hasCompactSupport hφc.mul_right
  have hc : Integrable (fun x => φ x * c) := hφi.mul_const c
  have hpoint (x : ℂ) : Real.circleAverage
      (fun y => wholePlaneCov (a * x + b) (a * y + b)) z r = A x + D x + c := by
    rw [← circleAverage_complex_affine, circleAverage_wholePlaneCov_complex_affine ha b z x hr]
    dsimp [A, D, c]
    ring
  rw [wholePlaneGFFCov_pairing_circle_inverse_complex_affine φ ha b z r]
  simp_rw [hpoint]
  have heq : (fun x => φ x * (A x + D x + c)) =
      (fun x => (φ x * A x + φ x * D x) + φ x * c) := by
    funext x
    ring
  have hadd : (∫ x, (φ x * A x + φ x * D x) + φ x * c) =
      (∫ x, φ x * A x) + (∫ x, φ x * D x) + (∫ x, φ x) * c := by
    have h₁ := integral_add (hAi.add hDi) hc
    have h₂ := integral_add hAi hDi
    simp only [Pi.add_apply, integral_mul_const] at h₁ h₂
    rw [h₁, h₂]
  rw [heq, hadd]
  rfl

/-- Recentered pairing-circle covariance is affine invariant at the kernel
level. Both the pairing and the circle are centered by the same reference
circle, with the pairing weighted by its total mass. -/
theorem wholePlaneGFFCov_recentered_pairing_circle_complex_affine
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {a : ℂ} (ha : a ≠ 0) (b z : ℂ) {r : ℝ} (hr : 0 < r) :
    (‖a‖ ^ 2)⁻¹ *
      (wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a)))
          (.circle (‖a‖ * r) (a * z + b)) -
        wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a))) (.circle ‖a‖ b)) -
      (∫ x, φ x) * (wholePlaneGFFCov (.circle ‖a‖ b)
        (.circle (‖a‖ * r) (a * z + b)) -
        wholePlaneGFFCov (.circle ‖a‖ b) (.circle ‖a‖ b)) =
    wholePlaneGFFCov (.pairing φ) (.circle r z) -
      wholePlaneGFFCov (.pairing φ) (.circle 1 0) -
      (∫ x, φ x) * (wholePlaneGFFCov (.circle 1 0) (.circle r z) -
        wholePlaneGFFCov (.circle 1 0) (.circle 1 0)) := by
  have hp := wholePlaneGFFCov_pairing_circle_complex_affine hφ hφc ha b z hr
  have hq := wholePlaneGFFCov_pairing_circle_complex_affine hφ hφc ha b 0
    (show (0 : ℝ) < 1 from zero_lt_one)
  have hcr := wholePlaneGFFCov_circles_complex_affine ha
    (show (0 : ℝ) < 1 from zero_lt_one) hr (w := (0 : ℂ)) (z := z) (b := b)
  have hcc := wholePlaneGFFCov_circles_complex_affine ha
    (show (0 : ℝ) < 1 from zero_lt_one) (show (0 : ℝ) < 1 from zero_lt_one)
    (w := (0 : ℂ)) (z := 0) (b := b)
  simp only [mul_one, mul_zero, zero_add] at hq hcr hcc
  rw [hp, hq, hcr, hcc]
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  field_simp
  ring

/-- The mixed covariance of the affine-recentered field agrees with the
original pairing-circle covariance. -/
theorem IsWholePlaneGFF.covariance_complex_affine_pairing_circle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    cov[fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x,
      fun ω => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b; P] =
      wholePlaneGFFCov (.pairing φ) (.circle r z) := by
  let _ := h.isProbabilityMeasure
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hψ := hφ.comp_inverse_complex_affine ha b
  have hlp (o : GFFObservable) (ho : o.IsAdmissible) :
      MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨o, ho⟩).memLp (by simp)
  have hp := hlp (.pairing (fun y => φ ((y - b) / a))) hψ
  have hq := hlp (.circle ‖a‖ b) ha'
  have hs := hlp (.circle (‖a‖ * r) (a * z + b)) (mul_pos ha' hr)
  simp only [GFFObservable.eval] at hp hq hs
  rw [covariance_fun_sub_fun_sub (hp.const_mul _) (hq.mul_const _) hs hq,
    covariance_const_mul_left, covariance_const_mul_left,
    covariance_mul_const_left, covariance_mul_const_left]
  have hpc := h.covariance_eq (.pairing (fun y => φ ((y - b) / a)))
    (.circle (‖a‖ * r) (a * z + b)) hψ (mul_pos ha' hr)
  have hpq := h.covariance_eq (.pairing (fun y => φ ((y - b) / a)))
    (.circle ‖a‖ b) hψ ha'
  have hqc := h.covariance_eq (.circle ‖a‖ b) (.circle (‖a‖ * r) (a * z + b))
    ha' (mul_pos ha' hr)
  have hqq := h.covariance_eq (.circle ‖a‖ b) (.circle ‖a‖ b) ha' ha'
  simp only [GFFObservable.eval] at hpc hpq hqc hqq
  rw [hpc, hpq, hqc, hqq]
  have hk := wholePlaneGFFCov_recentered_pairing_circle_complex_affine
    hφ.1.continuous hφ.2.1 ha b z hr
  have hz (o : GFFObservable) (ho : o.IsAdmissible) :
      wholePlaneGFFCov o (.circle 1 0) = 0 := by
    rw [← h.covariance_eq o (.circle 1 0) ho zero_lt_one]
    have he : (fun ω => hcirc ω 1 0) =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [h.ae_circleAverage_one_zero] with ω hω
      exact hω
    simp only [GFFObservable.eval]
    unfold ProbabilityTheory.covariance
    have hi := integral_congr_ae he
    simp only [integral_zero] at hi
    rw [hi]
    apply integral_eq_zero_of_ae
    filter_upwards [he] with ω hω
    simp [hω]
  have hz' : wholePlaneGFFCov (.circle 1 0) (.circle r z) = 0 := by
    rw [h.wholePlaneGFFCov_comm (.circle 1 0) (.circle r z) zero_lt_one hr]
    exact hz _ hr
  rw [hz (.pairing φ) hφ, hz', wholePlaneGFFCov_circle_one_zero] at hk
  simp only [sub_zero, mul_zero] at hk
  linarith

/-- Affine invariance reduces to the covariance of two pairings. -/
theorem IsWholePlaneGFF.complex_affine_of_pairing_pairing_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hcov : ∀ (φ ψ : ℂ → ℝ), IsTestFunction univ φ → IsTestFunction univ ψ →
      cov[fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
          hcirc ω ‖a‖ b * ∫ x, φ x,
        fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => ψ ((y - b) / a)) -
          hcirc ω ‖a‖ b * ∫ x, ψ x; P] =
        wholePlaneGFFCov (.pairing φ) (.pairing ψ)) :
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) := by
  apply h.complex_affine_of_pairing_covariance ha b
  intro φ hφ o ho
  cases o with
  | pairing ψ => exact hcov φ ψ hφ ho
  | circle r z => exact h.covariance_complex_affine_pairing_circle ha b hφ ho z

end HarmonicBalls
