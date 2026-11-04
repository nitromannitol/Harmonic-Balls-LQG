import HarmonicBalls.Proofs.Sec10.FrontierTwoComponents

/-! # Minimal separation without closedness restrictions

For two domains sharing a frontier and filling its complement, deleting any
nonempty part of the frontier makes its complement connected. -/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- An open set's regularization and its closure have the same frontier. -/
theorem IsOpen.frontier_interior_closure {X : Type*} [TopologicalSpace X]
    {G : Set X} (hG : IsOpen G) :
    frontier (interior (closure G)) = frontier (closure G) := by
  have hcl : closure (interior (closure G)) = closure G :=
    Subset.antisymm (closure_minimal interior_subset isClosed_closure)
      (closure_mono hG.subset_interior_closure)
  rw [frontier, frontier, hcl, isOpen_interior.interior_eq, closure_closure]

/-- Two connected domains that fill the complement of their common frontier
have a minimal separator: deleting any nonempty subset reconnects the whole
complement. The deleted subset need not be open or closed. -/
theorem isConnected_compl_frontier_sdiff_of_two_sides
    {X : Type*} [TopologicalSpace X] {U V S : Set X}
    (hU : IsConnected U) (hV : IsConnected V)
    (hfill : (frontier U)ᶜ = U ∪ V) (hVfront : frontier U ⊆ closure V)
    (hS : S ⊆ frontier U) (hne : S.Nonempty) :
    IsConnected (frontier U \ S)ᶜ := by
  have hsU : S ⊆ closure U := hS.trans frontier_subset_closure
  have hsV : S ⊆ closure V := hS.trans hVfront
  have hUS : IsPreconnected (U ∪ S) :=
    hU.isPreconnected.subset_closure subset_union_left (union_subset subset_closure hsU)
  have hVS : IsPreconnected (V ∪ S) :=
    hV.isPreconnected.subset_closure subset_union_left (union_subset subset_closure hsV)
  obtain ⟨a, ha⟩ := hne
  have hmeet : ((U ∪ S) ∩ (V ∪ S)).Nonempty := ⟨a, Or.inr ha, Or.inr ha⟩
  have heq : (frontier U \ S)ᶜ = (U ∪ S) ∪ (V ∪ S) := by
    ext x
    have hx : x ∈ (frontier U)ᶜ ↔ x ∈ U ∨ x ∈ V := by rw [hfill]; rfl
    simp only [mem_compl_iff, Set.mem_sdiff, mem_union] at hx ⊢
    tauto
  rw [heq]
  exact ⟨hU.nonempty.mono (subset_union_left.trans subset_union_left),
    hUS.union' hmeet hVS⟩

/-- For a connected open set with connected closed-set complement, deleting
any nonempty part of its frontier reconnects its complement. -/
theorem isConnected_compl_frontier_sdiff_of_connected_compl_closure
    {G S : Set ℂ} (hGo : IsOpen G) (hG : IsConnected G)
    (hC : IsConnected (closure G)ᶜ)
    (hS : S ⊆ frontier ((closure G)ᶜ)) (hne : S.Nonempty) :
    IsConnected (frontier ((closure G)ᶜ) \ S)ᶜ := by
  have hfill : (frontier ((closure G)ᶜ))ᶜ =
      (closure G)ᶜ ∪ interior (closure G) := by
    rw [compl_frontier_eq_union_interior, isClosed_closure.isOpen_compl.interior_eq,
      compl_compl]
  have hfront : frontier ((closure G)ᶜ) ⊆ closure (interior (closure G)) := by
    rw [frontier_compl, ← IsOpen.frontier_interior_closure hGo]
    exact frontier_subset_closure
  exact isConnected_compl_frontier_sdiff_of_two_sides hC
    (IsConnected.interior_closure_of_isOpen hG hGo) hfill hfront hS hne

/-- Under volume growth and Lemma 10.5, deleting any nonempty part of a
compactly contained cluster's complementary frontier makes the complement
connected. The crossing-containment hypothesis is explicit. -/
theorem ae_cluster_frontier_deletion_compl_connected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ∀ S ⊆ frontier U, S.Nonempty → IsConnected (frontier U \ S)ᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_component_eq_and_frontier_of_crossing hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_compl_closure_connected_of_crossing_containment hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω heq hconn hcluster
  intro t ht z hz hcl U hU S hS hne
  have hG := hcluster t 1 ht zero_lt_one z hz
  rw [(heq t ht z hz hcl U hU).1] at hS ⊢
  exact isConnected_compl_frontier_sdiff_of_connected_compl_closure hG.1 hG.2.1
    (hconn t ht z hz hcl) hS hne

end HarmonicBalls
