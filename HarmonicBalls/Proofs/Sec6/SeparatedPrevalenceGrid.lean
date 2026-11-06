import HarmonicBalls.Proofs.Sec6.SingularShrinkingOriginCommonRadii

/-! # Separated approximation by the prevalence grid

The imported count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- A unit-disc point sufficiently far from the origin has a nearby
prevalence-grid point that stays outside a prescribed origin ball. -/
theorem exists_prevalenceGrid_dist_lt_of_separated
    {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) {w : ℂ}
    (hw : w ∈ ball 0 1) (hsep : 10 * Real.sqrt t + 2 * (t/100) + R ≤ ‖w‖) :
    ∃ z ∈ prevalenceGrid t, dist w z < 2 * (t/100) ∧ R ≤ ‖z‖ := by
  obtain ⟨z, hz, hd⟩ := exists_scaledLattice_dist_lt w (show 0 < t/100 by positivity)
  have hwout : dist w 0 < 1 := hw
  have hzout := dist_triangle z w 0
  have hzin := dist_triangle w z 0
  have hsym : dist z w = dist w z := dist_comm z w
  have hnorm : R ≤ ‖z‖ := by
    simp only [dist_zero_right] at hzin
    linarith [Real.sqrt_nonneg t]
  refine ⟨z, ⟨⟨?_, ?_⟩, hz⟩, hd, hnorm⟩
  · change dist z 0 < 1+t
    linarith
  · change ¬ dist z 0 < 10 * Real.sqrt t
    simp only [dist_zero_right] at hzin ⊢
    linarith

end HarmonicBalls.Section6
