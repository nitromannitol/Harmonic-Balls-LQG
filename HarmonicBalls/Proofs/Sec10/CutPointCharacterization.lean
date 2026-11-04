import HarmonicBalls.Proofs.Sec10.CutPointSeparation

/-!
# Cut points and nonseparating decompositions

For a common frontier, a cut point is exactly a singleton intersection of two
closed pieces which separately do not separate the two domains.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Proper closed pieces meeting at one point disconnect their union when that
point is removed. -/
theorem not_isPreconnected_sdiff_singleton_of_closed_decomposition
    {S A B : Set ℂ} {a : ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B = S) (hab : A ∩ B = {a})
    (hAp : ∃ x ∈ S, x ∉ A) (hBp : ∃ x ∈ S, x ∉ B) :
    ¬ IsPreconnected (S \ {a}) := by
  intro hp
  have haA : a ∈ A := (show a ∈ A ∩ B from hab.symm ▸ mem_singleton a).1
  have haB : a ∈ B := (show a ∈ A ∩ B from hab.symm ▸ mem_singleton a).2
  have hcover : S \ {a} ⊆ A ∪ B := by rw [hAB]; exact sdiff_subset
  have hdis : (S \ {a}) ∩ (A ∩ B) = ∅ := by
    rw [hab]
    exact Set.eq_empty_iff_forall_notMem.mpr (by
      rintro x ⟨hx, hxa⟩
      exact hx.2 hxa)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hp) A B hA hB hcover hdis with h | h
  · obtain ⟨x, hxS, hxA⟩ := hAp
    have hxa : x ∉ ({a} : Set ℂ) := by
      intro hxa
      exact hxA (mem_singleton_iff.mp hxa ▸ haA)
    exact hxA (h ⟨hxS, hxa⟩)
  · obtain ⟨x, hxS, hxB⟩ := hBp
    have hxa : x ∉ ({a} : Set ℂ) := by
      intro hxa
      exact hxB (mem_singleton_iff.mp hxa ▸ haB)
    exact hxB (h ⟨hxS, hxa⟩)

/-- A cut point of a common frontier is equivalent to a singleton-intersection
closed decomposition whose two pieces each fail to separate the domains. -/
theorem cut_point_iff_nonseparating_frontier_decomposition
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y a : ℂ}
    (hx : x ∈ G) (hy : y ∈ U) (ha : a ∈ frontier U) :
    ¬ IsPreconnected (frontier U \ {a}) ↔
      ∃ A B : Set ℂ, IsClosed A ∧ IsClosed B ∧ A ∪ B = frontier U ∧
        A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
        y ∈ connectedComponentIn Bᶜ x := by
  constructor
  · intro hcut
    obtain ⟨A, B, hA, hB, hAB, hab, hAx, hBx, _⟩ :=
      cut_point_yields_nonseparating_frontier_decomposition hGo hGc hUo hUc hdis hfront hx hy ha hcut
    exact ⟨A, B, hA, hB, hAB, hab, hAx, hBx⟩
  · rintro ⟨A, B, hA, hB, hAB, hab, hAx, hBx⟩
    have hsep := (frontier_minimal_closed_separator hGo hGc hUo hUc hdis hfront hx hy).1
    have hAs : A ⊆ frontier U := by rw [← hAB]; exact subset_union_left
    have hBs : B ⊆ frontier U := by rw [← hAB]; exact subset_union_right
    have hAp : ∃ z ∈ frontier U, z ∉ A := by
      apply not_subset.mp
      intro hs
      have heq : A = frontier U := Subset.antisymm hAs hs
      exact hsep (heq ▸ hAx)
    have hBp : ∃ z ∈ frontier U, z ∉ B := by
      apply not_subset.mp
      intro hs
      have heq : B = frontier U := Subset.antisymm hBs hs
      exact hsep (heq ▸ hBx)
    exact not_isPreconnected_sdiff_singleton_of_closed_decomposition hA hB hAB hab hAp hBp

/-- When the frontier is compact, the two nonseparating pieces may be taken
compact. -/
theorem cut_point_iff_compact_nonseparating_frontier_decomposition
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) (hcompact : IsCompact (frontier U))
    {x y a : ℂ} (hx : x ∈ G) (hy : y ∈ U) (ha : a ∈ frontier U) :
    ¬ IsPreconnected (frontier U \ {a}) ↔
      ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ A ∪ B = frontier U ∧
        A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
        y ∈ connectedComponentIn Bᶜ x := by
  rw [cut_point_iff_nonseparating_frontier_decomposition hGo hGc hUo hUc hdis hfront hx hy ha]
  constructor
  · rintro ⟨A, B, hA, hB, hAB, hab, hAx, hBx⟩
    have hAs : A ⊆ frontier U := by rw [← hAB]; exact subset_union_left
    have hBs : B ⊆ frontier U := by rw [← hAB]; exact subset_union_right
    exact ⟨A, B, hcompact.of_isClosed_subset hA hAs, hcompact.of_isClosed_subset hB hBs,
      hAB, hab, hAx, hBx⟩
  · rintro ⟨A, B, hA, hB, hAB, hab, hAx, hBx⟩
    exact ⟨A, B, hA.isClosed, hB.isClosed, hAB, hab, hAx, hBx⟩

/-- Almost surely, every cut point of a complementary cluster frontier is
characterized by a compact nonseparating singleton-intersection decomposition. -/
theorem ae_cluster_cut_point_iff_compact_nonseparating_decomposition
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U, ∀ a ∈ frontier U,
      ¬ IsPreconnected (frontier U \ {a}) ↔
        ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ A ∪ B = frontier U ∧
          A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
          y ∈ connectedComponentIn Bᶜ x := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU x hx y hy a ha
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨v, hv, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (cluster (μ ω) 1 z t) U := by
    rw [disjoint_left]
    intro w hw hwU
    exact hUs hwU (subset_closure hw)
  have hfrontcompact : IsCompact (frontier U) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_frontier
      (fun q hq => ball_subset_closedBall (hg.2.2.2.2 (subset_closure hq)))
  exact cut_point_iff_compact_nonseparating_frontier_decomposition hc.1 hc.2.1 hg.1 hg.2.1
    hdis hg.2.2.2.1 hfrontcompact hx hy ha

end HarmonicBalls
