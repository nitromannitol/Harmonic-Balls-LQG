import HarmonicBalls.Proofs.Sec6.ScaledCriterionThreeGrid

/-! # Rescaling an annular lattice with a prescribed phase -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- After normalization and translation, an annular lattice with any fixed
phase lies in the prevalence grid. -/
theorem scaled_phase_annulus_lattice_subset_prevalenceGrid
    {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 9 ≤ n) (x phase : ℂ) :
    ∃ y : ℂ, ∀ z ∈ annulus x (s / 2) s,
      z - phase ∈ scaledLattice (dyadicScale n * s / 100) →
      s⁻¹ • z - y ∈ prevalenceGrid (dyadicScale n) := by
  obtain ⟨y, hy⟩ := scaled_annulus_lattice_subset_prevalenceGrid hs hn (x - phase)
  refine ⟨y + s⁻¹ • phase, ?_⟩
  intro z hz hlat
  have hz' : z - phase ∈ annulus (x - phase) (s / 2) s := by
    simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      sub_sub_sub_cancel_right] using hz
  have h := hy (z - phase) ⟨hlat, hz'⟩
  have heq : s⁻¹ • (z - phase) - y = s⁻¹ • z - (y + s⁻¹ • phase) := by
    rw [smul_sub]
    abel
  rwa [heq] at h

end HarmonicBalls.Section6
