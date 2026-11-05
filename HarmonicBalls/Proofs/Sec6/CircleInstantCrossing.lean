import HarmonicBalls.Proofs.Sec6.AnnulusBoundaryRegularity
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Immediate Brownian crossings of a circle -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set MarkovProcess Metric
open scoped ENNReal NNReal Topology InnerProductSpace

/-- Brownian motion started on a circle immediately leaves its closed disc. -/
theorem ae_planarBrownian_exit_closedBall_of_mem_sphere
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : dist y z = r) :
    ∀ᵐ ω ∂planarBrownianMotion y, ContinuousPath.exitTime (closedBall z r) ω = 0 := by
  have hd : y - z ≠ 0 := by
    intro h
    have : dist y z = 0 := by rw [dist_eq_zero]; exact sub_eq_zero.mp h
    linarith
  apply ae_planarBrownian_exitTime_closed_eq_zero_of_exterior_cone y
    (closedBall z r) (radialCone (y - z)) (isOpen_radialCone _) (radialCone_nonempty hd)
    (fun a ha v => smul_mem_radialCone_iff _ _ ha)
  intro w hw hmem
  have hh := radialCone_outside_closedBall hr hy hw
  exact (not_lt_of_ge (mem_closedBall.mp hmem)) hh

/-- Brownian motion started on a circle immediately enters its open disc. -/
theorem ae_planarBrownian_exit_compl_ball_of_mem_sphere
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : dist y z = r) :
    ∀ᵐ ω ∂planarBrownianMotion y, ContinuousPath.exitTime (ball z r)ᶜ ω = 0 := by
  have hd : z - y ≠ 0 := by
    intro h
    have : dist y z = 0 := by rw [dist_eq_zero]; exact (sub_eq_zero.mp h).symm
    linarith
  apply ae_planarBrownian_exitTime_eq_zero_of_local_exterior_cone y
    (ball z r)ᶜ (radialCone (z - y)) (isOpen_radialCone _) (radialCone_nonempty hd)
    (fun a ha v => smul_mem_radialCone_iff _ _ ha) hr
  intro w hw hsmall hmem
  exact hmem (mem_ball.mpr (radialCone_inside_ball hr hy hw hsmall))

/-- If a path exits one set instantly, it leaves that set before any positive
exit time from another set. -/
theorem exists_not_mem_before_exitTime_of_exitTime_eq_zero
    (F U : Set ℂ) (ω : ContinuousPath ℂ) (hF : ContinuousPath.exitTime F ω = 0)
    (hU : 0 < ContinuousPath.exitTime U ω) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ContinuousPath.exitTime U ω ∧ ω t ∉ F := by
  by_contra h
  have hle : ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime F ω := by
    rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    exact le_of_not_gt (fun hlt => h ⟨t, hlt, ht⟩)
  rw [hF] at hle
  exact (not_lt_of_ge hle) hU

/-- Before leaving any open neighbourhood of its starting point on a circle,
Brownian motion visits both the interior and exterior of the circle. -/
theorem ae_planarBrownian_visits_both_sides_before_exit
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    {U : Set ℂ} (hU : IsOpen U) (hyU : y ∈ U) :
    ∀ᵐ ω ∂planarBrownianMotion y,
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < ContinuousPath.exitTime U ω ∧ dist (ω t) z < r) ∧
      (∃ t : ℝ≥0, (t : ℝ≥0∞) < ContinuousPath.exitTime U ω ∧ r < dist (ω t) z) := by
  filter_upwards [ae_planarBrownian_exit_closedBall_of_mem_sphere hr hy,
    ae_planarBrownian_exit_compl_ball_of_mem_sphere hr hy,
    ae_planarBrownianMotion_exitTime_pos hU hyU] with ω hout hin hpos
  obtain ⟨s, hs, hs'⟩ := exists_not_mem_before_exitTime_of_exitTime_eq_zero _ _ ω hin hpos
  obtain ⟨t, ht, ht'⟩ := exists_not_mem_before_exitTime_of_exitTime_eq_zero _ _ ω hout hpos
  exact ⟨⟨s, hs, by simpa only [mem_compl_iff, not_not, mem_ball] using hs'⟩,
    ⟨t, ht, by simpa only [mem_closedBall, not_le] using ht'⟩⟩

end HarmonicBalls.Section6
