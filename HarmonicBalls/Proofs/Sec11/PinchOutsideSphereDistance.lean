import HarmonicBalls.Proofs.Sec11.PinchOutsideCircleBuffers
import HarmonicBalls.Proofs.Sec11.PinchOutsideRadialTests
import HarmonicBalls.Steps.Sec11.LocalExtremaRepresentatives
import HarmonicBalls.Steps.Sec11.PinchLocalSetDist

/-! # Locality of the inner sphere separation -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The small ball containing both pinch spheres is disjoint from the core. -/
theorem IsCorrectedPinchConfiguration.inner_sphere_ball_subset_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ball (0 : ℂ) (3 * δ) ⊆ (closure W)ᶜ := by
  obtain ⟨η, hη, hgap⟩ := h.exists_core_radial_gap
  intro z hz hzW
  have hz' : ‖z‖ < 3 * δ := by simpa [mem_ball, dist_zero_right] using hz
  have hw := (hgap z hzW).1
  have hδ := h.δ₀_mem.2
  nlinarith

/-- The distance between the two pinch spheres is an infimum of internal
metric distances inside the radius-three-delta ball. -/
theorem ofReal_setDist_inner_spheres_eq_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (setDist D (sphere 0 δ) (sphere 0 (2 * δ))) =
      ⨅ x ∈ sphere (0 : ℂ) δ, ⨅ y ∈ sphere (0 : ℂ) (2 * δ),
        internalMetric D (ball 0 (3 * δ)) x y := by
  have h2 : 0 < 2 * δ := by positivity
  have hA : sphere (0 : ℂ) δ ⊆ ball 0 (2 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  have hcl : closure (ball (0 : ℂ) (2 * δ)) ⊆ ball 0 (3 * δ) := by
    rw [closure_ball (0 : ℂ) h2.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hn : (frontier (ball (0 : ℂ) (2 * δ))).Nonempty := by
    rw [frontier_ball (0 : ℂ) h2.ne']
    exact NormedSpace.sphere_nonempty.mpr h2.le
  have hh := ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hA hcl
    (NormedSpace.sphere_nonempty.mpr hδ.le) hn
  rwa [frontier_ball (0 : ℂ) h2.ne'] at hh

/-- A local representative of the internal metric on the radius-three-delta
ball gives a local representative of the separation of the pinch spheres. -/
theorem exists_local_pinch_sphere_distance_representative
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {D : Ω → ℂ → ℂ → ℝ} {G : Ω → ℂ → ℂ → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hG : ∀ x ∈ sphere (0 : ℂ) δ, ∀ y ∈ sphere (0 : ℂ) (2 * δ),
      Measurable[m] (fun ω => G ω x y))
    (hEq : ∀ᵐ ω ∂P, ∀ x ∈ sphere (0 : ℂ) δ, ∀ y ∈ sphere (0 : ℂ) (2 * δ),
      internalMetric (D ω) (ball 0 (3 * δ)) x y = G ω x y) :
    ∃ a : Ω → ℝ≥0∞, Measurable[m] a ∧
      a =ᵐ[P] fun ω => ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) := by
  have hA : sphere (0 : ℂ) δ ⊆ ball 0 (3 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  have hB : sphere (0 : ℂ) (2 * δ) ⊆ ball 0 (3 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  obtain ⟨a, ha, hae⟩ := @exists_local_iInf_internalMetric_representative Ω m₀ P m D G
    (ball 0 (3 * δ)) (sphere 0 δ) (sphere 0 (2 * δ)) isOpen_ball hA hB hmetric hG hEq
  refine ⟨a, ha, ?_⟩
  filter_upwards [hae, hmetric] with ω haω hmω
  rw [ofReal_setDist_inner_spheres_eq_internalMetric hmω hδ]
  exact haω.symm

#print axioms IsCorrectedPinchConfiguration.inner_sphere_ball_subset_outside
#print axioms ofReal_setDist_inner_spheres_eq_internalMetric
#print axioms exists_local_pinch_sphere_distance_representative
end HarmonicBalls
