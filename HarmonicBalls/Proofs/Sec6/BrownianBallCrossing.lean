import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Crossing concentric balls

A continuous path started inside a smaller ball reaches its boundary strictly
before exiting a larger concentric ball, provided that the larger exit is finite.
This is the pathwise crossing used in the fine-support hitting argument.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set MarkovProcess Metric
open scoped ENNReal

/-- If the outer exit time is finite, a path started in the inner ball reaches
its boundary strictly before it leaves the larger ball. -/
theorem exitTime_ball_lt_outer_and_mem_sphere {x : ℂ} {r R : ℝ}
    (hrR : r < R) (ω : ContinuousPath ℂ) (h0 : ω 0 ∈ ball x r)
    (hfinite : ContinuousPath.exitTime (ball x R) ω ≠ ∞) :
    ContinuousPath.exitTime (ball x r) ω < ContinuousPath.exitTime (ball x R) ω ∧
      ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal) ∈ sphere x r := by
  have hle : ContinuousPath.exitTime (ball x r) ω ≤ ContinuousPath.exitTime (ball x R) ω :=
    ContinuousPath.exitTime_mono (ball_subset_ball hrR.le) ω
  have hinner : ContinuousPath.exitTime (ball x r) ω ≠ ∞ :=
    ne_top_of_le_ne_top hfinite hle
  have hsp : ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal) ∈ sphere x r :=
    frontier_ball_subset_sphere (ContinuousPath.coordinate_exitTime_mem_frontier
      (ball x r) isOpen_ball ω h0 hinner)
  refine ⟨lt_of_le_of_ne hle ?_, hsp⟩
  intro heq
  have h0' : ω 0 ∈ ball x R := ball_subset_ball hrR.le h0
  have hout : ω ((ContinuousPath.exitTime (ball x R) ω).toNNReal) ∈ sphere x R :=
    frontier_ball_subset_sphere (ContinuousPath.coordinate_exitTime_mem_frontier
      (ball x R) isOpen_ball ω h0' hfinite)
  rw [← heq] at hout
  have hdist1 : dist (ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal)) x = r := hsp
  have hdist2 : dist (ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal)) x = R := hout
  linarith

/-- Finite exit from the inner ball is already enough: the outer exit may be
infinite, in which case the strict ordering is automatic. -/
theorem exitTime_ball_lt_outer_and_mem_sphere_of_inner_finite {x : ℂ} {r R : ℝ}
    (hrR : r < R) (ω : ContinuousPath ℂ) (h0 : ω 0 ∈ ball x r)
    (hfinite : ContinuousPath.exitTime (ball x r) ω ≠ ∞) :
    ContinuousPath.exitTime (ball x r) ω < ContinuousPath.exitTime (ball x R) ω ∧
      ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal) ∈ sphere x r := by
  by_cases hout : ContinuousPath.exitTime (ball x R) ω = ∞
  · rw [hout]
    refine ⟨lt_top_iff_ne_top.mpr hfinite, ?_⟩
    exact frontier_ball_subset_sphere (ContinuousPath.coordinate_exitTime_mem_frontier
      (ball x r) isOpen_ball ω h0 hfinite)
  · exact exitTime_ball_lt_outer_and_mem_sphere hrR ω h0 hout

/-- The same crossing holds almost surely for planar Brownian motion on any
full-measure event on which the outer exit is finite. -/
theorem ae_planarBrownian_ball_crossing {x : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hfinite : ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (ball x R) ω ≠ ∞) :
    ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (ball x r) ω < ContinuousPath.exitTime (ball x R) ω ∧
      ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal) ∈ sphere x r := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x, hfinite] with ω h0 hfin
  apply exitTime_ball_lt_outer_and_mem_sphere hrR ω _ hfin
  simpa [h0] using hr

/-- Hitting any member of a family before exit also hits its union before exit.
Thus lower bounds obtained by compact approximation pass to the union. -/
theorem iSup_hitting_probability_le_union (x : ℂ) (U : Set ℂ) (K : ℕ → Set ℂ) :
    (⨆ n, planarBrownianMotion x
      {ω | ContinuousPath.exitTime (K n)ᶜ ω ≤ ContinuousPath.exitTime U ω}) ≤
    planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤ ContinuousPath.exitTime U ω} := by
  apply iSup_le
  intro n
  apply measure_mono
  intro ω hω
  exact (ContinuousPath.exitTime_mono (compl_subset_compl.mpr (subset_iUnion K n)) ω).trans hω

end HarmonicBalls.Section6
