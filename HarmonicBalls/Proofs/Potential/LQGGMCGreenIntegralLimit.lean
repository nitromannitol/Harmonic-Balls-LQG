import HarmonicBalls.Proofs.Potential.GreenGeneralIdentification

/-!
# Local control of Green integrals

A Riesz moment controls the Green integral near its pole uniformly over measures.
-/

open MeasureTheory Metric Set

namespace HarmonicBalls

/-- A bound on a Riesz moment gives quantitative small-ball control of the Green kernel. -/
theorem green_integral_ball_le_of_riesz_bound {O : Set ℂ} {R a K r : ℝ}
    (hO : IsOpen O) (hR : 0 < R) (hOR : O ⊆ ball (0 : ℂ) R)
    (ha : 0 < a) (hr : 0 < r) (x : ℂ) (ν : Measure ℂ)
    (hint : Integrable (fun y => ‖x - y‖ ^ (-(2 * a))) ν)
    (hbound : (∫ y, ‖x - y‖ ^ (-(2 * a)) ∂ν) ≤ K) :
    IntegrableOn (greenFunction O x) (ball x r) ν ∧
      (∫ y in ball x r, greenFunction O x y ∂ν) ≤
        ((2 * Real.pi)⁻¹ * (a⁻¹ * (2 * R) ^ a)) * r ^ a * K := by
  let C : ℝ := (2 * Real.pi)⁻¹ * (a⁻¹ * (2 * R) ^ a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrpow : 0 ≤ r ^ a := Real.rpow_nonneg hr.le _
  have hpt : ∀ y ∈ ball x r, greenFunction O x y ≤
      C * r ^ a * ‖x - y‖ ^ (-(2 * a)) := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp [greenFunction_self, Real.zero_rpow (by linarith : -(2 * a) ≠ 0)]
    · have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hyx))
      have hdr : ‖x - y‖ ≤ r := by
        simpa [dist_comm, dist_eq_norm] using (mem_ball.mp hy).le
      have hp : ‖x - y‖ ^ a ≤ r ^ a := Real.rpow_le_rpow hd.le hdr ha.le
      have heq : ‖x - y‖ ^ (-a) = ‖x - y‖ ^ a * ‖x - y‖ ^ (-(2 * a)) := by
        rw [← Real.rpow_add hd]
        congr 1; ring
      calc
        greenFunction O x y ≤ C * ‖x - y‖ ^ (-a) :=
          GreenGeneral.greenFunction_le_mul_rpow_neg hR hOR ha hyx
        _ = C * ‖x - y‖ ^ a * ‖x - y‖ ^ (-(2 * a)) := by rw [heq]; ring
        _ ≤ C * r ^ a * ‖x - y‖ ^ (-(2 * a)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC)
            (Real.rpow_nonneg hd.le _)
  have hdom : IntegrableOn (fun y => C * r ^ a * ‖x - y‖ ^ (-(2 * a))) (ball x r) ν :=
    (hint.const_mul (C * r ^ a)).integrableOn
  have hgreen0 : ∀ y, 0 ≤ greenFunction O x y :=
    greenFunction_nonneg (isBounded_ball.subset hOR) x
  have hgreen : IntegrableOn (greenFunction O x) (ball x r) ν :=
    hdom.mono' (measurable_greenFunction hO x).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball (fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgreen0 y)]
        exact hpt y hy))
  refine ⟨hgreen, ?_⟩
  calc
    (∫ y in ball x r, greenFunction O x y ∂ν) ≤
        ∫ y in ball x r, C * r ^ a * ‖x - y‖ ^ (-(2 * a)) ∂ν :=
      integral_mono_ae hgreen hdom
        (ae_restrict_of_forall_mem measurableSet_ball hpt)
    _ = C * r ^ a * ∫ y in ball x r, ‖x - y‖ ^ (-(2 * a)) ∂ν :=
      integral_const_mul _ _
    _ ≤ C * r ^ a * ∫ y, ‖x - y‖ ^ (-(2 * a)) ∂ν := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hrpow)
      exact setIntegral_le_integral hint (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤ C * r ^ a * K := mul_le_mul_of_nonneg_left hbound (mul_nonneg hC hrpow)

/-- Polynomial ball growth and finite mass give a quantitative local Green bound. -/
theorem green_integral_ball_le_of_mass_growth {O : Set ℂ} {R a β A m r : ℝ}
    (hO : IsOpen O) (hR : 0 < R) (hOR : O ⊆ ball (0 : ℂ) R)
    (ha : 0 < a) (hβ : 2 * a < β) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hr : 0 < r) (x : ℂ) (ν : Measure ℂ)
    (hν : ν univ ≤ ENNReal.ofReal m)
    (hball : ∀ t, 0 < t → ν (closedBall x t) ≤ ENNReal.ofReal (A * t ^ β)) :
    IntegrableOn (greenFunction O x) (ball x r) ν ∧
      (∫ y in ball x r, greenFunction O x y ∂ν) ≤
        ((2 * Real.pi)⁻¹ * (a⁻¹ * (2 * R) ^ a)) * r ^ a *
          (m + A * ((2 * a) / (β - 2 * a))) := by
  have h2a : 0 < 2 * a := by positivity
  have hK : 0 ≤ m + A * ((2 * a) / (β - 2 * a)) := by positivity
  have hmoment := integrable_norm_sub_rpow_neg hK
    (lintegral_norm_sub_rpow_neg_le h2a hβ hm hA hν hball)
  exact green_integral_ball_le_of_riesz_bound hO hR hOR ha hr x ν hmoment.1 hmoment.2

end HarmonicBalls
