import HarmonicBalls.Proofs.Sec10.FrontierMinimalSeparation

/-!
# Cut points and minimal separators

A cut point of a closed set produces two proper closed subsets whose union is
the set and whose intersection is the cut point. For a minimal
separator, neither of these subsets separates the distinguished points.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Decompose a closed set at a cut point into two proper closed pieces. -/
theorem closed_decomposition_of_not_preconnected_sdiff_singleton
    {S : Set ℂ} (hS : IsClosed S) {a : ℂ} (ha : a ∈ S)
    (hcut : ¬ IsPreconnected (S \ {a})) :
    ∃ A B : Set ℂ, IsClosed A ∧ IsClosed B ∧ A ⊆ S ∧ B ⊆ S ∧
      A ∪ B = S ∧ A ∩ B = {a} ∧ (∃ x ∈ S, x ∉ A) ∧ (∃ y ∈ S, y ∉ B) := by
  classical
  have hneg : ¬ ∀ u v : Set ℂ, IsClosed u → IsClosed v →
      S \ {a} ⊆ u ∪ v → (S \ {a}) ∩ (u ∩ v) = ∅ →
        S \ {a} ⊆ u ∨ S \ {a} ⊆ v := by
    intro h
    exact hcut (isPreconnected_iff_subset_of_disjoint_closed.mpr h)
  push Not at hneg
  obtain ⟨u, v, hu, hv, hcover, hdis, hnu, hnv⟩ := hneg
  obtain ⟨x, hxs, hxu⟩ := not_subset.mp hnu
  obtain ⟨y, hys, hyv⟩ := not_subset.mp hnv
  let A := S ∩ (u ∪ {a})
  let B := S ∩ (v ∪ {a})
  have hAc : IsClosed A := hS.inter (hu.union isClosed_singleton)
  have hBc : IsClosed B := hS.inter (hv.union isClosed_singleton)
  refine ⟨A, B, hAc, hBc, inter_subset_left, inter_subset_left, ?_, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      by_cases hza : z = a
      · exact Or.inl ⟨hz, Or.inr (by simpa using hza)⟩
      · have hzs : z ∈ S \ {a} := ⟨hz, by simpa using hza⟩
        rcases hcover hzs with hzu | hzv
        · exact Or.inl ⟨hz, Or.inl hzu⟩
        · exact Or.inr ⟨hz, Or.inl hzv⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨hzS, hzA⟩, _, hzB⟩
      by_cases hza : z = a
      · simpa using hza
      · have hzs : z ∈ S \ {a} := ⟨hzS, by simpa using hza⟩
        have hzu : z ∈ u := hzA.resolve_right (by simpa using hza)
        have hzv : z ∈ v := hzB.resolve_right (by simpa using hza)
        have hempty : z ∈ (∅ : Set ℂ) := hdis ▸ ⟨hzs, hzu, hzv⟩
        exact hempty.elim
    · intro z hz
      have hza : z = a := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨ha, Or.inr (mem_singleton a)⟩, ⟨ha, Or.inr (mem_singleton a)⟩⟩
  · refine ⟨x, hxs.1, ?_⟩
    rintro ⟨_, hxu' | hxa⟩
    · exact hxu hxu'
    · exact hxs.2 hxa
  · refine ⟨y, hys.1, ?_⟩
    rintro ⟨_, hyv' | hya⟩
    · exact hyv hyv'
    · exact hys.2 hya

/-- A cut point of a common frontier would yield two closed nonseparating
pieces whose union separates the connected open sets. -/
theorem cut_point_yields_nonseparating_frontier_decomposition
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y a : ℂ}
    (hx : x ∈ G) (hy : y ∈ U) (ha : a ∈ frontier U)
    (hcut : ¬ IsPreconnected (frontier U \ {a})) :
    ∃ A B : Set ℂ, IsClosed A ∧ IsClosed B ∧ A ∪ B = frontier U ∧
      A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
      y ∈ connectedComponentIn Bᶜ x ∧
      y ∉ connectedComponentIn (A ∪ B)ᶜ x := by
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAB, hABa, hAproper, hBproper⟩ :=
    closed_decomposition_of_not_preconnected_sdiff_singleton isClosed_frontier ha hcut
  have hsep := frontier_minimal_closed_separator hGo hGc hUo hUc hdis hfront hx hy
  refine ⟨A, B, hAc, hBc, hAB, hABa, hsep.2 A hAc hAs hAproper,
    hsep.2 B hBc hBs hBproper, ?_⟩
  simpa only [hAB] using hsep.1


/-- Almost surely, a cut point on a complementary cluster frontier would
produce two closed nonseparating pieces whose union does separate. -/
theorem ae_cluster_cut_point_separation_obstruction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U, ∀ a ∈ frontier U,
      ¬ IsPreconnected (frontier U \ {a}) →
      ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ A ∪ B = frontier U ∧
        A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
        y ∈ connectedComponentIn Bᶜ x ∧
        y ∉ connectedComponentIn (A ∪ B)ᶜ x := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU x hx y hy a ha hcut
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
  obtain ⟨A, B, hAc, hBc, hAB, hABa, hAx, hBx, hABx⟩ :=
    cut_point_yields_nonseparating_frontier_decomposition hc.1 hc.2.1 hg.1 hg.2.1
      hdis hg.2.2.2.1 hx hy ha hcut
  have hAs : A ⊆ frontier U := by rw [← hAB]; exact subset_union_left
  have hBs : B ⊆ frontier U := by rw [← hAB]; exact subset_union_right
  exact ⟨A, B, hfrontcompact.of_isClosed_subset hAc hAs,
    hfrontcompact.of_isClosed_subset hBc hBs, hAB, hABa, hAx, hBx, hABx⟩

end HarmonicBalls
