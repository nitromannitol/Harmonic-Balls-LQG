import HarmonicBalls.Proofs.Sec9.AffineMixedCovariance
import HarmonicBalls.Proofs.Sec9.WholePlaneCovAffine
import HarmonicBalls.Proofs.Sec8.CircleDensityDoubleLog

/-! # Affine transformation of pairing covariances

The diagonal of the whole-plane kernel is negligible for planar measure.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- The covariance potential of a compactly supported continuous density is
continuous, without a restriction on its total mass. -/
theorem continuous_wholePlaneCov_potential_of_compact_support {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fun x => ∫ y, g y * wholePlaneCov x y) := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have heq (x : ℂ) : (∫ y, g y * wholePlaneCov x y) =
      (∫ y, g y) * wholePlaneNormalization x +
        (∫ y, g y * wholePlaneNormalization y) - ∫ y, g y * Real.log ‖y - x‖ := by
    have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
      have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
        ).integrable_smul_right_of_hasCompactSupport hg hgc
      simpa only [smul_eq_mul, mul_comm] using h
    have hpoint : (∫ y, g y * wholePlaneCov x y) =
        ∫ y, (g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) -
          g y * Real.log ‖y - x‖ := by
      apply integral_congr_ae
      filter_upwards [ae_ne_complex x] with y hy
      rw [wholePlaneCov_eq_log_sub hy.symm, norm_sub_rev]
      simp only [wholePlaneNormalization]
      ring
    have hsub := integral_sub ((hgi.mul_const (wholePlaneNormalization x)).add hni) hli
    have hadd := integral_add (hgi.mul_const (wholePlaneNormalization x)) hni
    simp only [Pi.add_apply] at hsub hadd
    rw [hpoint, hsub, hadd, integral_mul_const]
  simp_rw [heq]
  exact ((continuous_const.mul continuous_wholePlaneNormalization).add continuous_const).sub
    (continuous_log_potential_of_compact_support hg hgc)

/-- The affine change of the covariance potential for an arbitrary compactly
supported continuous density. -/
theorem integral_mul_wholePlaneCov_complex_affine {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {a : ℂ} (ha : a ≠ 0)
    (b x : ℂ) :
    (∫ y, g y * wholePlaneCov (a * x + b) (a * y + b)) =
      (∫ y, g y * wholePlaneCov x y) +
      (∫ y, g y) * (wholePlaneNormalization (a * x + b) - wholePlaneNormalization x) +
      (∫ y, g y * (wholePlaneNormalization (a * y + b) - wholePlaneNormalization y)) -
      (∫ y, g y) * Real.log ‖a‖ := by
  let D : ℂ → ℝ := fun y => wholePlaneNormalization (a * y + b) - wholePlaneNormalization y
  have hD : Continuous D := (continuous_wholePlaneNormalization.comp (by fun_prop)).sub
    continuous_wholePlaneNormalization
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hki : Integrable (fun y => g y * wholePlaneCov x y) :=
    integrable_mul_wholePlaneCov hg hgc x
  have hdi : Integrable (fun y => g y * D y) :=
    (hg.mul hD).integrable_of_hasCompactSupport hgc.mul_right
  have heq : (∫ y, g y * wholePlaneCov (a * x + b) (a * y + b)) =
      ∫ y, ((g y * wholePlaneCov x y + g y * D x) + g y * D y) -
        g y * Real.log ‖a‖ := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex x] with y hy
    rw [wholePlaneCov_comp_affine ha hy.symm]
    dsimp [D, wholePlaneNormalization]
    ring
  have hsub := integral_sub ((hki.add (hgi.mul_const (D x))).add hdi)
    (hgi.mul_const (Real.log ‖a‖))
  have hadd₁ := integral_add (hki.add (hgi.mul_const (D x))) hdi
  have hadd₂ := integral_add hki (hgi.mul_const (D x))
  simp only [Pi.add_apply] at hsub hadd₁ hadd₂
  rw [heq, hsub, hadd₁, hadd₂, integral_mul_const, integral_mul_const]

/-- Affine transformation of the covariance of two compactly supported
continuous test densities. -/
theorem wholePlaneGFFCov_pairings_complex_affine
    {φ ψ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    wholePlaneGFFCov (.pairing (fun x => φ ((x - b) / a)))
      (.pairing (fun y => ψ ((y - b) / a))) =
      (‖a‖ ^ 2) ^ 2 * (wholePlaneGFFCov (.pairing φ) (.pairing ψ) +
        (∫ y, ψ y) * (∫ x, φ x * (wholePlaneNormalization (a * x + b) -
          wholePlaneNormalization x)) +
        (∫ x, φ x) * ((∫ y, ψ y * (wholePlaneNormalization (a * y + b) -
          wholePlaneNormalization y)) - (∫ y, ψ y) * Real.log ‖a‖)) := by
  let P : ℂ → ℝ := fun x => ∫ y, ψ y * wholePlaneCov x y
  let D : ℂ → ℝ := fun x => wholePlaneNormalization (a * x + b) - wholePlaneNormalization x
  let m : ℝ := ∫ y, ψ y
  let c : ℝ := (∫ y, ψ y * D y) - m * Real.log ‖a‖
  have hP : Continuous P := continuous_wholePlaneCov_potential_of_compact_support hψ hψc
  have hD : Continuous D := (continuous_wholePlaneNormalization.comp (by fun_prop)).sub
    continuous_wholePlaneNormalization
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hPi : Integrable (fun x => φ x * P x) :=
    (hφ.mul hP).integrable_of_hasCompactSupport hφc.mul_right
  have hDi : Integrable (fun x => φ x * D x) :=
    (hφ.mul hD).integrable_of_hasCompactSupport hφc.mul_right
  have hpoint (x : ℂ) : (∫ y, ψ y * wholePlaneCov (a * x + b) (a * y + b)) =
      P x + m * D x + c := by
    rw [integral_mul_wholePlaneCov_complex_affine hψ hψc ha b x]
    dsimp [P, D, m, c]
    ring
  rw [wholePlaneGFFCov_pairings_inverse_complex_affine φ ψ ha b]
  simp_rw [hpoint]
  have heq : (fun x => φ x * (P x + m * D x + c)) =
      fun x => (φ x * P x + m * (φ x * D x)) + φ x * c := by
    funext x
    ring
  have hadd₁ := integral_add (hPi.add (hDi.const_mul m)) (hφi.mul_const c)
  have hadd₂ := integral_add hPi (hDi.const_mul m)
  simp only [Pi.add_apply, integral_const_mul, integral_mul_const] at hadd₁ hadd₂
  rw [heq, hadd₁, hadd₂]
  rfl

/-- The covariance with the reference circle vanishes for every admissible
observable of the normalized whole-plane field. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_circle_one_zero_right
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable) (ho : o.IsAdmissible) :
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

/-- The covariance of two affine-recentered pairings agrees with their
original covariance at the kernel level. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_recentered_pairings_complex_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) :
    ((‖a‖ ^ 2)⁻¹) ^ 2 * wholePlaneGFFCov
        (.pairing (fun x => φ ((x - b) / a))) (.pairing (fun y => ψ ((y - b) / a))) -
      (‖a‖ ^ 2)⁻¹ * (∫ y, ψ y) * wholePlaneGFFCov
        (.pairing (fun x => φ ((x - b) / a))) (.circle ‖a‖ b) -
      (‖a‖ ^ 2)⁻¹ * (∫ x, φ x) * wholePlaneGFFCov
        (.circle ‖a‖ b) (.pairing (fun y => ψ ((y - b) / a))) +
      (∫ x, φ x) * (∫ y, ψ y) * wholePlaneGFFCov (.circle ‖a‖ b) (.circle ‖a‖ b) =
      wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
  have hψ' := hψ.comp_inverse_complex_affine ha b
  have hp := wholePlaneGFFCov_pairings_complex_affine hφ.1.continuous hφ.2.1
    hψ.1.continuous hψ.2.1 ha b
  have hq := wholePlaneGFFCov_pairing_circle_complex_affine hφ.1.continuous hφ.2.1
    ha b 0 (show (0 : ℝ) < 1 from zero_lt_one)
  have hs := wholePlaneGFFCov_pairing_circle_complex_affine hψ.1.continuous hψ.2.1
    ha b 0 (show (0 : ℝ) < 1 from zero_lt_one)
  have hqq := wholePlaneGFFCov_circles_complex_affine ha zero_lt_one zero_lt_one
    (w := (0 : ℂ)) (z := 0) (b := b)
  simp only [mul_one, mul_zero, zero_add] at hq hs hqq
  rw [h.wholePlaneGFFCov_circle_one_zero_right (.pairing φ) hφ] at hq
  rw [h.wholePlaneGFFCov_circle_one_zero_right (.pairing ψ) hψ] at hs
  rw [wholePlaneGFFCov_circle_one_zero] at hqq
  rw [h.wholePlaneGFFCov_comm (.circle ‖a‖ b)
    (.pairing (fun y => ψ ((y - b) / a))) (norm_pos_iff.mpr ha) hψ', hp, hq, hs, hqq]
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  field_simp
  ring

/-- Pairing-pairing covariance is invariant under affine pullback and
subtraction of the transformed reference circle. -/
theorem IsWholePlaneGFF.covariance_complex_affine_pairings
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) :
    cov[fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x,
      fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => ψ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, ψ x; P] =
      wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
  let _ := h.isProbabilityMeasure
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hφ' := hφ.comp_inverse_complex_affine ha b
  have hψ' := hψ.comp_inverse_complex_affine ha b
  have hlp (o : GFFObservable) (ho : o.IsAdmissible) :
      MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨o, ho⟩).memLp (by simp)
  have hp := hlp (.pairing (fun y => φ ((y - b) / a))) hφ'
  have hs := hlp (.pairing (fun y => ψ ((y - b) / a))) hψ'
  have hq := hlp (.circle ‖a‖ b) ha'
  simp only [GFFObservable.eval] at hp hs hq
  rw [covariance_fun_sub_fun_sub (hp.const_mul _) (hq.mul_const _)
    (hs.const_mul _) (hq.mul_const _)]
  simp only [covariance_const_mul_left, covariance_mul_const_left,
    covariance_const_mul_right, covariance_mul_const_right]
  have hpp := h.covariance_eq (.pairing (fun y => φ ((y - b) / a)))
    (.pairing (fun y => ψ ((y - b) / a))) hφ' hψ'
  have hpq := h.covariance_eq (.pairing (fun y => φ ((y - b) / a))) (.circle ‖a‖ b) hφ' ha'
  have hqp := h.covariance_eq (.circle ‖a‖ b) (.pairing (fun y => ψ ((y - b) / a))) ha' hψ'
  have hqq := h.covariance_eq (.circle ‖a‖ b) (.circle ‖a‖ b) ha' ha'
  simp only [GFFObservable.eval] at hpp hpq hqp hqq
  rw [hpp, hpq, hqp, hqq]
  have hk := h.wholePlaneGFFCov_recentered_pairings_complex_affine ha b hφ hψ
  nlinarith

/-- A nonconstant complex affine pullback of the whole-plane GFF, normalized
by subtracting its transformed unit circle average, is again a whole-plane
GFF. -/
theorem IsWholePlaneGFF.complex_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) := by
  apply h.complex_affine_of_pairing_pairing_covariance ha b
  intro φ ψ hφ hψ
  exact h.covariance_complex_affine_pairings ha b hφ hψ

end HarmonicBalls
