import HarmonicBalls.Proofs.Sec10.UniqueComplementFrontier

/-! # The two sides of a complementary frontier

For a connected open set with connected complement of its closure, the
frontier of the exterior component has exactly two complementary components:
the exterior and the interior of the set's closure. -/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- The interior of the closure of a connected open set is connected. -/
theorem IsConnected.interior_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {G : Set X} (hG : IsConnected G) (hGo : IsOpen G) :
    IsConnected (interior (closure G)) := by
  have hsub : G ⊆ interior (closure G) := hGo.subset_interior_iff.mpr subset_closure
  exact ⟨hG.nonempty.mono hsub, hG.isPreconnected.subset_closure hsub interior_subset⟩

/-- Two disjoint connected open sets are exactly the connected components
of their union. -/
theorem connectedComponentsIn_union_of_disjoint_isOpen_isConnected
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUo : IsOpen U) (hVo : IsOpen V) (hU : IsConnected U) (hV : IsConnected V)
    (hdis : Disjoint U V) : connectedComponentsIn (U ∪ V) = {U, V} := by
  have hUcomp : ∀ x ∈ U, connectedComponentIn (U ∪ V) x = U := by
    intro x hx
    apply Subset.antisymm
    · apply isPreconnected_connectedComponentIn.subset_left_of_subset_union hUo hVo hdis
        (connectedComponentIn_subset _ _)
      exact ⟨x, mem_connectedComponentIn (Or.inl hx), hx⟩
    · exact hU.isPreconnected.subset_connectedComponentIn hx subset_union_left
  have hVcomp : ∀ x ∈ V, connectedComponentIn (U ∪ V) x = V := by
    intro x hx
    apply Subset.antisymm
    · apply isPreconnected_connectedComponentIn.subset_right_of_subset_union hUo hVo hdis
        (connectedComponentIn_subset _ _)
      exact ⟨x, mem_connectedComponentIn (Or.inr hx), hx⟩
    · exact hV.isPreconnected.subset_connectedComponentIn hx subset_union_right
  ext W
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · simp [hUcomp x hx]
    · simp [hVcomp x hx]
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with rfl | rfl
    · obtain ⟨x, hx⟩ := hU.nonempty
      exact ⟨x, Or.inl hx, hUcomp x hx⟩
    · obtain ⟨x, hx⟩ := hV.nonempty
      exact ⟨x, Or.inr hx, hVcomp x hx⟩

/-- If the complement of the closure is connected, the frontier of that
complement has exactly two complementary components. -/
theorem connectedComponentsIn_compl_frontier_compl_closure
    {G : Set ℂ} (hGo : IsOpen G) (hG : IsConnected G)
    (hC : IsConnected (closure G)ᶜ) :
    connectedComponentsIn (frontier (closure G)ᶜ)ᶜ =
      {(closure G)ᶜ, interior (closure G)} := by
  have hdis : Disjoint (closure G)ᶜ (interior (closure G)) := by
    exact disjoint_compl_left.mono_right interior_subset
  rw [compl_frontier_eq_union_interior, isClosed_closure.isOpen_compl.interior_eq,
    compl_compl]
  exact connectedComponentsIn_union_of_disjoint_isOpen_isConnected
    isClosed_closure.isOpen_compl isOpen_interior hC (IsConnected.interior_closure_of_isOpen hG hGo) hdis

/-- Assuming volume growth and Lemma 10.5, every compactly contained
cluster's complementary frontier has exactly two complementary components.
The crossing-containment assumption remains explicit. -/
theorem ae_cluster_frontier_has_two_complement_components
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        connectedComponentsIn (frontier U)ᶜ =
          {U, interior (closure (cluster (μ ω) 1 z t))} := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_component_eq_and_frontier_of_crossing hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_compl_closure_connected_of_crossing_containment hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω heq hconn hcluster
  intro t ht z hz hcl U hU
  have hG := hcluster t 1 ht zero_lt_one z hz
  rw [(heq t ht z hz hcl U hU).1]
  exact connectedComponentsIn_compl_frontier_compl_closure hG.1 hG.2.1
    (hconn t ht z hz hcl)

end HarmonicBalls
