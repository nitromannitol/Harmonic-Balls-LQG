import HarmonicBalls.Proofs.Sec5.InteriorGreenComparison
import HarmonicBalls.Proofs.Sec4.GreenBalayage

/-! # Interior Green-function correction for bounded open domains -/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter

/-- The greatest harmonic minorant of the Newtonian kernel is harmonic on
a bounded open domain containing its pole. -/
theorem harmonicOnNhd_greatestHarmonicMinorant_newtonKernel
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {z : ℂ} (hz : z ∈ U) :
    HarmonicOnNhd (fun y => (greatestHarmonicMinorant U (newtonKernelEReal z) y).toReal) U := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  obtain ⟨R, hR⟩ := hUb.subset_ball z
  have hminor := isHarmonicMinorant_const_newtonKernelEReal (hR.trans ball_subset_closedBall)
  have hreg := (isHarmonicMinorant_regularized_iff hε hball).1 hminor
  have hlow : ∀ y ∈ U, -(2 * Real.pi)⁻¹ * Real.log R ≤ regularizedNewtonKernel ε z y := by
    intro y hy
    exact EReal.coe_le_coe_iff.mp (hreg.2 y hy)
  have hcont : ContinuousOn (regularizedNewtonKernel ε z) U :=
    (continuous_regularizedNewtonKernel_right hε z).continuousOn
  have hmean := hasLocalSuperMean_regularizedNewtonKernel hε z U
  have hsweep := (sweep_limit hU hcont hmean hreg.1 hlow).1
  intro y hy
  apply (harmonicAt_congr_nhds ?_).2 (hsweep y hy)
  filter_upwards [hU.mem_nhds hy] with w hw
  rw [greatestHarmonicMinorant_regularized hε hball,
    greatestHarmonicMinorant_eq_of_sweep_limit hU hcont hmean hreg.1 hlow w hw,
    EReal.toReal_coe]

/-- The difference between the Green functions of a bounded open set and an
enclosing disc extends harmonically across the pole on the open set. -/
theorem exists_harmonicOnNhd_greenFunction_difference
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) {r : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h U ∧ ∀ x ∈ U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x := by
  let h : ℂ → ℝ := fun x => greatestHarmonicMinorantBall r z x -
    (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal
  have hh : HarmonicOnNhd h U :=
    ((isHarmonicMinorant_greatestHarmonicMinorantBall (hsub hz)).1.mono hsub).sub
      (harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hU hUb hz)
  refine ⟨h, hh, ?_⟩
  intro x hx hxz
  have hzx : z ≠ x := Ne.symm hxz
  simp only [greenFunction, hz, hx, hsub hz, hsub hx, true_and,
    greatestHarmonicMinorant_ball (hsub hz) (hsub hx), EReal.toReal_coe, h]
  rw [ite_eq_left hzx, ite_eq_left hzx]
  ring

/-- One direction of general-domain cluster comparison needs only admissibility
of the general-domain least supersolution when the domain is bounded and open. -/
theorem cluster_subset_clusterOn_of_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U)
    {r t : ℝ} {z : ℂ} (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    cluster μ r z t ⊆ clusterOn μ U z t := by
  obtain ⟨h, hh, hG⟩ := exists_harmonicOnNhd_greenFunction_difference hU
    (isBounded_ball.subset hsub) hsub hz
  exact cluster_subset_clusterOn_of_interior_green_difference hU hsub hz hv hh hG hcl

end HarmonicBalls
