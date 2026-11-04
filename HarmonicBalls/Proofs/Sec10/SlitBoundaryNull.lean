import HarmonicBalls.Proofs.Sec10.SlitBarrierObstruction
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Null frontier of a slit annulus

The deterministic slit obstruction persists even when the open set has
Lebesgue-null frontier. No LQG realization is asserted.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory

/-- The real axis has zero planar Lebesgue measure. -/
theorem volume_complex_real_axis : volume {z : ℂ | z.im = 0} = 0 := by
  change volume (LinearMap.ker Complex.imLm : Set ℂ) = 0
  apply Measure.addHaar_submodule
  rw [ne_eq, LinearMap.ker_eq_top]
  intro h
  have hI := congrArg (fun f : ℂ →ₗ[ℝ] ℝ => f Complex.I) h
  simp at hI

/-- The frontier of a slit annulus is contained in the two boundary
circles and the real axis. -/
theorem frontier_slit_annulus_subset (r R : ℝ) :
    frontier (annulus 0 r R ∩ Complex.slitPlane) ⊆
      sphere (0 : ℂ) r ∪ sphere 0 R ∪ {z : ℂ | z.im = 0} := by
  have hslit : frontier Complex.slitPlane ⊆ {z : ℂ | z.im = 0} := by
    have hclosed : IsClosed {z : ℂ | z.im = 0} :=
      isClosed_eq Complex.continuous_im continuous_const
    have hsub : Complex.slitPlaneᶜ ⊆ {z : ℂ | z.im = 0} := by
      intro z hz
      by_contra h
      exact hz (Or.inr h)
    rw [← frontier_compl Complex.slitPlane]
    exact frontier_subset_closure.trans (closure_minimal hsub hclosed)
  have hann : frontier (annulus (0 : ℂ) r R) ⊆
      sphere 0 r ∪ sphere 0 R := by
    change frontier (ball (0 : ℂ) R ∩ (closedBall 0 r)ᶜ) ⊆ _
    intro z hz
    rcases frontier_inter_subset _ _ hz with hz | hz
    · exact Or.inr (frontier_ball_subset_sphere hz.1)
    · exact Or.inl (frontier_closedBall_subset_sphere (by simpa only [frontier_compl] using hz.2))
  intro z hz
  rcases frontier_inter_subset _ _ hz with hz | hz
  · exact Or.inl (hann hz.1)
  · exact Or.inr (hslit hz.2)

/-- A slit annulus has Lebesgue-null frontier, despite the possible hole
created by closing its slit. -/
theorem volume_frontier_slit_annulus (r R : ℝ) :
    volume (frontier (annulus 0 r R ∩ Complex.slitPlane)) = 0 := by
  apply measure_mono_null (frontier_slit_annulus_subset r R)
  exact measure_union_null
    (measure_union_null (Measure.addHaar_sphere volume 0 r) (Measure.addHaar_sphere volume 0 R))
    volume_complex_real_axis

end HarmonicBalls
