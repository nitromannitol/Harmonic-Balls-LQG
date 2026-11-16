import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic

/-!
# Circle averages of the disc Green function

The exact circle average gives bounded approximations to the logarithmic pole.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set
open ComplexConjugate

/-- The circle average of the Newtonian kernel has a logarithmic cutoff at the radius. -/
theorem circleAverage_newtonKernel_eq_log_max {x y : ℂ} {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (newtonKernel y) x r =
      -(2 * Real.pi)⁻¹ * Real.log (max r ‖y - x‖) := by
  by_cases hyx : ‖y - x‖ ≤ r
  · rw [max_eq_left hyx, circleAverage_newtonKernel hr hyx]
  · have hdist : r < ‖y - x‖ := lt_of_not_ge hyx
    rw [max_eq_right hdist.le]
    have hharm : InnerProductSpace.HarmonicOnNhd (newtonKernel y) (closedBall x |r|) := by
      intro w hw
      refine harmonicAt_newtonKernel fun hwy => ?_
      rw [hwy, mem_closedBall, abs_of_pos hr, dist_eq_norm] at hw
      linarith
    rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm, newtonKernel]

/-- Averaging the disc Green kernel cuts off its logarithmic singularity at the circle radius. -/
theorem circleAverage_greenFunction_ball_eq_log_max {R : ℝ} {x y : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ ball (0 : ℂ) R) (hsub : closedBall x r ⊆ ball 0 R) :
    Real.circleAverage (greenFunction (ball 0 R) y) x r =
      -(2 * Real.pi)⁻¹ * Real.log (max r ‖y - x‖) -
        greatestHarmonicMinorantBall R y x := by
  have hR : 0 < R := (norm_nonneg y).trans_lt (mem_ball_zero_iff.1 hy)
  have hsph : sphere x |r| ⊆ ball 0 R := by
    rw [abs_of_pos hr]
    exact sphere_subset_closedBall.trans hsub
  have hharm : InnerProductSpace.HarmonicOnNhd (greatestHarmonicMinorantBall R y) (closedBall x |r|) := by
    intro w hw
    rw [abs_of_pos hr] at hw
    exact harmonicAt_greatestHarmonicMinorantBall (norm_pos_iff.1 (norm_sub_conj_mul_pos hR
      (mem_ball_zero_iff.1 hy) (mem_ball_zero_iff.1 (hsub hw)).le))
  have hcae : greenFunction (ball 0 R) y =ᶠ[codiscreteWithin (sphere x |r|)]
      fun w => newtonKernel y w - greatestHarmonicMinorantBall R y w := by
    show {w | greenFunction (ball 0 R) y w = newtonKernel y w - greatestHarmonicMinorantBall R y w} ∈ _
    rw [mem_codiscreteWithin]
    intro p _
    rw [disjoint_principal_right]
    have hy' : ({y} : Set ℂ)ᶜ ∈ 𝓝[≠] p := by
      by_cases hp : p = y
      · rw [hp]
        exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hp)
    refine mem_of_superset hy' fun w hw hwS => hwS.2 ?_
    exact greenFunction_ball_eq_sub hy (hsph hwS.1) (Ne.symm hw)
  have hNi : CircleIntegrable (newtonKernel y) x r := by
    have h := (circleIntegrable_log_norm_sub_const (a := y) (c := x) r).const_smul (a := -(2 * Real.pi)⁻¹)
    refine (circleIntegrable_congr (fun w _ => ?_)).1 h
    simp [newtonKernel, norm_sub_rev, smul_eq_mul]
  have hhi : CircleIntegrable (greatestHarmonicMinorantBall R y) x r :=
    ContinuousOn.circleIntegrable' fun w hw =>
      (hharm w (sphere_subset_closedBall hw)).1.continuousAt.continuousWithinAt
  rw [Real.circleAverage_congr_codiscreteWithin hcae hr.ne', Real.circleAverage_fun_sub hNi hhi,
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm, circleAverage_newtonKernel_eq_log_max hr]

end HarmonicBalls
