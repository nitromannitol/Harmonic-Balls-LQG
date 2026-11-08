import HarmonicBalls.Proofs.Sec11.PinchOutsideQDistance
import HarmonicBalls.Proofs.Sec11.PinchOutsideCenterDistance

/-! # Outside locality of the crossing distances

The local metric decoder uses Leonardo Bonanno's LatticeProb formalization.
-/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The three full-plane crossing distances in the buffered pinch construction
have simultaneous versions measurable in the outside field modulo constants. -/
theorem IsCorrectedPinchConfiguration.exists_outside_crossing_distances
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ L a₀ a₁ : Ω → ℝ≥0∞,
      (∀ f ∈ ({L, a₀, a₁} : Set (Ω → ℝ≥0∞)), @Measurable Ω ℝ≥0∞
        (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ f) ∧
      ∀ᵐ ω ∂P,
        L ω = ENNReal.ofReal (setDist (𝔇 (hC ω)) (closure Q') (frontier Q)) ∧
        a₀ ω = ENNReal.ofReal (setDist (𝔇 (hC ω)) {0} (sphere 0 δ)) ∧
        a₁ ω = ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ))) := by
  have hQopen : IsOpen Q := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isOpen_Q
  have hQsub : closure Q' ⊆ Q := by
    have ht : 0 < 10 * δ := by have := h.δ₀_mem.1; positivity
    exact (self_subset_thickening ht _).trans (subset_closure.trans h.buffer_Q')
  have hQne : (closure Q').Nonempty :=
    h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isConnected_Q'.nonempty.mono subset_closure
  have hfront : (frontier Q).Nonempty := by
    have hp := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.setDist_frontier_pos isEuclideanLengthMetric_dist
    by_contra hn
    have he : frontier Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he, setDist] at hp
  have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  obtain ⟨G, hG, hGe⟩ := h.exists_outside_internal_baseMetric_on_complement hgff 𝔇 h𝔇
  have hA : closure Q' ⊆ (closure W)ᶜ := hQsub.trans (subset_closure.trans h.closure_Q_subset_outside)
  have hB : frontier Q ⊆ (closure W)ᶜ := frontier_subset_closure.trans h.closure_Q_subset_outside
  obtain ⟨L, hL, hLe⟩ := @exists_local_iInf_internalMetric_representative Ω m₀ P
    (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
    (fun ω => 𝔇 (hC ω)) G (closure W)ᶜ (closure Q') (frontier Q) isClosed_closure.isOpen_compl
    hA hB hm (fun x _ y _ => hG x y)
    (hGe.mono fun _ hw x hx y hy => hw x (hA hx) y (hB hy))
  obtain ⟨a₀, ha₀, ha₀e⟩ := h.exists_outside_baseMetric_center_distance hgff 𝔇 h𝔇
  obtain ⟨a₁, ha₁, ha₁e⟩ := h.exists_outside_baseMetric_sphere_distance hgff 𝔇 h𝔇
  refine ⟨L, a₀, a₁, ?_, ?_⟩
  · intro f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl <;> assumption
  · filter_upwards [hLe, ha₀e, ha₁e, hm] with ω hLω h₀ h₁ hD
    refine ⟨?_, h₀, h₁⟩
    rw [ofReal_setDist_boundary_eq_internalMetric hD hQopen hQsub
      h.closure_Q_subset_outside hQne hfront]
    exact hLω.symm

#print axioms IsCorrectedPinchConfiguration.exists_outside_crossing_distances
end HarmonicBalls
