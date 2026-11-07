import HarmonicBalls.Proofs.Sec11.PinchOutsideFullMetric
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstRepresentative

/-! # Outside locality of the Q-boundary separation

The underlying centered metric decoder uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The closure of the outer obstacle is disjoint from the core. -/
theorem IsCorrectedPinchConfiguration.closure_Q_subset_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    closure Q ⊆ (closure W)ᶜ := by
  have ht : 0 < 10 * δ := by have := h.δ₀_mem.1; positivity
  have hWT : closure W ⊆ closure T := by
    intro x hx
    apply subset_closure
    exact (h.buffer_W (subset_closure (self_subset_thickening ht _ hx))).1
  intro x hx hxW
  have hq := h.buffer_Q (subset_closure (self_subset_thickening ht _ hx))
  exact hq.2 (self_subset_thickening ht _ (hWT hxW))

/-- The inner obstacle is contained in the open outer obstacle. -/
theorem IsCorrectedPinchConfiguration.inner_Q_subset_Q
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) : Q' ⊆ Q := by
  have ht : 0 < 10 * δ := by have := h.δ₀_mem.1; positivity
  intro x hx
  exact h.buffer_Q' (subset_closure (self_subset_thickening ht _ (subset_closure hx)))

/-- The outer-obstacle boundary separation has an outside-field measurable
version for the whole-plane GFF base metric. -/
theorem IsCorrectedPinchConfiguration.exists_outside_baseMetric_Q_distance
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a ∧
      a =ᵐ[P] fun ω => ENNReal.ofReal (setDist (𝔇 (hC ω)) Q' (frontier Q)) := by
  have hQopen : IsOpen Q := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isOpen_Q
  have hQne : Q'.Nonempty := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isConnected_Q'.nonempty
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
  have hA : Q' ⊆ (closure W)ᶜ := h.inner_Q_subset_Q.trans (subset_closure.trans h.closure_Q_subset_outside)
  have hB : frontier Q ⊆ (closure W)ᶜ := frontier_subset_closure.trans h.closure_Q_subset_outside
  obtain ⟨a, ha, hae⟩ := @exists_local_iInf_internalMetric_representative Ω m₀ P
    (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
    (fun ω => 𝔇 (hC ω)) G (closure W)ᶜ Q' (frontier Q) isClosed_closure.isOpen_compl
    hA hB hm (fun x _ y _ => hG x y)
    (hGe.mono fun _ hw x hx y hy => hw x (hA hx) y (hB hy))
  refine ⟨a, ha, ?_⟩
  filter_upwards [hae, hm] with ω he hw
  rw [ofReal_setDist_boundary_eq_internalMetric hw hQopen h.inner_Q_subset_Q
    h.closure_Q_subset_outside hQne hfront]
  exact he.symm

#print axioms IsCorrectedPinchConfiguration.closure_Q_subset_outside
#print axioms IsCorrectedPinchConfiguration.inner_Q_subset_Q
#print axioms IsCorrectedPinchConfiguration.exists_outside_baseMetric_Q_distance
end HarmonicBalls
