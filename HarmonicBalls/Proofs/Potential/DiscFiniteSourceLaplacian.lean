import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-!
# Disc Green potentials of finite sources

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- The Green kernel is integrable against a finite source and planar volume,
when the source is concentrated in the closed disc. -/
theorem disc_green_integrable_product_volume {ν : Measure ℂ} [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    Integrable (fun p : ℂ × ℂ => greenFunction (ball 0 R) p.1 p.2)
      (ν.prod (volume.restrict (ball 0 R))) := by
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume (ball z r) ≤ ENNReal.ofReal (r ^ (1 : ℝ)) := by
    intro r hr hrr z hz
    exact (hg r hr hrr z hz).2
  have h := green_disc_integrable_product_of_upper (ν := ν) hR hr₀ (by norm_num : (0 : ℝ) < 1)
    hup (measure_ball_lt_top (μ := volume)).ne
  rw [Measure.restrict_eq_self_of_ae_mem hν] at h
  exact h

/-- The totalized finite-source potential is integrable on the disc. -/
theorem integrableOn_disc_greenPotential {ν : Measure ℂ} [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    IntegrableOn (greenPotential (ball 0 R) ν) (ball 0 R) := by
  have h := (disc_green_integrable_product_volume hR hν).integral_prod_right
  apply h.congr
  filter_upwards with x
  change (∫ y, greenFunction (ball 0 R) y x ∂ν) = greenPotential (ball 0 R) ν x
  unfold greenPotential
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R y x)

/-- A finite measure concentrated in a disc has the expected distributional
Laplacian, including when it has atoms. -/
theorem hasLaplacian_disc_greenPotential {ν : Measure ℂ} [IsFiniteMeasure ν]
    {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R) :
    HasLaplacian (greenPotential (ball 0 R) ν) 0 ν (ball 0 R) := by
  have hνc : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R := hν.mono fun _ hy => ball_subset_closedBall hy
  refine ⟨(integrableOn_disc_greenPotential hR hνc).locallyIntegrableOn, fun φ hφ => ?_⟩
  refine ⟨integrable_zero_measure, hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hΔc.continuousOn
  have hp := disc_green_integrable_product_volume hR hνc
  have hw : Integrable (fun p : ℂ × ℂ => greenFunction (ball 0 R) p.1 p.2 * Δ φ p.2)
      (ν.prod (volume.restrict (ball 0 R))) := by
    apply hp.mul_bdd (hΔc.measurable.comp measurable_snd).aestronglyMeasurable
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_ball.preimage measurable_snd)).mpr (Filter.Eventually.of_forall fun _ =>
      ae_restrict_mem measurableSet_ball)] with p hp
    exact hB p.2 (ball_subset_closedBall hp)
  have hzero : ∀ x, x ∉ ball (0 : ℂ) R → Δ φ x = 0 := fun x hx =>
    laplacian_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
  calc
    ∫ x, greenPotential (ball 0 R) ν x * Δ φ x =
        ∫ x in ball (0 : ℂ) R, greenPotential (ball 0 R) ν x * Δ φ x := by
          symm
          exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])
    _ = ∫ x in ball (0 : ℂ) R, ∫ y, greenFunction (ball 0 R) y x * Δ φ x ∂ν := by
          apply integral_congr_ae
          filter_upwards with x
          rw [integral_mul_const]
          unfold greenPotential
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R x y)
    _ = ∫ y, (∫ x in ball (0 : ℂ) R, greenFunction (ball 0 R) y x * Δ φ x) ∂ν :=
          (integral_integral_swap hw).symm
    _ = ∫ y, -φ y ∂ν := by
          apply integral_congr_ae
          filter_upwards [hν] with y hy
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hzero x hx])]
          have h := ((greenFunctionBall R hR y hy).1.2 φ hφ).2.2
          simpa using h
    _ = (∫ x, φ x ∂(0 : Measure ℂ)) - ∫ x, φ x ∂ν := by rw [integral_zero_measure, zero_sub, integral_neg]


end HarmonicBalls
