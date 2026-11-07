import HarmonicBalls.Proofs.Sec11.PinchOutsideBaseMetric

/-! # Outside locality of the center-to-sphere separation

The underlying centered metric decoder uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- First exit from the inner ball computes center-to-sphere distance using
only the internal metric in the ball of radius `3 * δ`. -/
theorem ofReal_setDist_center_pinch_sphere_eq_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (setDist D {0} (sphere 0 δ)) =
      ⨅ y ∈ sphere (0 : ℂ) δ, internalMetric D (ball 0 (3 * δ)) 0 y := by
  have hsub : ({0} : Set ℂ) ⊆ ball 0 δ := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_ball_self hδ
  have hcl : closure (ball (0 : ℂ) δ) ⊆ ball 0 (3 * δ) := by
    rw [closure_ball (0 : ℂ) hδ.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hn : (frontier (ball (0 : ℂ) δ)).Nonempty := by
    rw [frontier_ball (0 : ℂ) hδ.ne']
    exact NormedSpace.sphere_nonempty.mpr hδ.le
  have hh := ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hsub hcl
    (Set.singleton_nonempty (0 : ℂ)) hn
  rw [frontier_ball (0 : ℂ) hδ.ne'] at hh
  simpa only [iInf_singleton] using hh

/-- Center-to-sphere distance for the base metric has an outside-field
measurable version. -/
theorem IsCorrectedPinchConfiguration.exists_outside_baseMetric_center_distance
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a ∧
      a =ᵐ[P] fun ω => ENNReal.ofReal (setDist (𝔇 (hC ω)) {0} (sphere 0 δ)) := by
  have hδ := h.δ₀_mem.1
  have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  obtain ⟨G, hG, hGe⟩ := h.exists_outside_internal_baseMetric hgff 𝔇 h𝔇
  have hA : ({0} : Set ℂ) ⊆ ball 0 (3 * δ) := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact mem_ball_self (by positivity)
  have hB : sphere (0 : ℂ) δ ⊆ ball 0 (3 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  obtain ⟨a, ha, hae⟩ := @exists_local_iInf_internalMetric_representative Ω m₀ P
    (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
    (fun ω => 𝔇 (hC ω)) G (ball 0 (3 * δ)) {0} (sphere 0 δ) isOpen_ball hA hB hm
    (fun x _ y _ => hG x y)
    (hGe.mono fun _ hw x hx y hy => hw x (hA hx) y (hB hy))
  refine ⟨a, ha, ?_⟩
  filter_upwards [hae, hm] with ω he hw
  rw [ofReal_setDist_center_pinch_sphere_eq_internalMetric hw hδ]
  simpa only [iInf_singleton] using he.symm

#print axioms ofReal_setDist_center_pinch_sphere_eq_internalMetric
#print axioms IsCorrectedPinchConfiguration.exists_outside_baseMetric_center_distance
end HarmonicBalls
