import HarmonicBalls.Proofs.Sec10.CutPointSeparation

/-!
# Connected pieces at a cut point

A closed decomposition of a connected set whose pieces meet at a single
point has connected pieces. This refines the cut-point decomposition used in
the complementary-frontier separation argument.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- If two closed sets meet in a singleton and their union is preconnected,
then each of the two sets is preconnected. -/
theorem isPreconnected_left_of_union_inter_singleton
    {A B : Set ℂ} {a : ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hab : A ∩ B = {a}) (hunion : IsPreconnected (A ∪ B)) :
    IsPreconnected A := by
  have haA : a ∈ A := by
    have : a ∈ A ∩ B := hab.symm ▸ mem_singleton a
    exact this.1
  apply isPreconnected_iff_subset_of_disjoint_closed.mpr
  intro u v hu hv hcover hdis
  have step (u v : Set ℂ) (hu : IsClosed u) (hv : IsClosed v)
      (hcover : A ⊆ u ∪ v) (hdis : A ∩ (u ∩ v) = ∅) (hav : a ∈ v) :
      A ⊆ u ∨ A ⊆ v := by
    have hnau : a ∉ u := by
      intro hau
      have : a ∈ (∅ : Set ℂ) := hdis ▸ ⟨haA, hau, hav⟩
      exact this.elim
    have hsub : A ∪ B ⊆ (u ∩ A) ∪ (v ∪ B) := by
      rintro x (hx | hx)
      · rcases hcover hx with hxu | hxv
        · exact Or.inl ⟨hxu, hx⟩
        · exact Or.inr (Or.inl hxv)
      · exact Or.inr (Or.inr hx)
    have hdis' : (A ∪ B) ∩ ((u ∩ A) ∩ (v ∪ B)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨_, ⟨hxu, hxA⟩, hxv | hxB⟩
      · have : x ∈ (∅ : Set ℂ) := hdis ▸ ⟨hxA, hxu, hxv⟩
        exact this.elim
      · have hxa : x = a := mem_singleton_iff.mp (hab ▸ ⟨hxA, hxB⟩)
        exact hnau (hxa ▸ hxu)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hunion) (u ∩ A) (v ∪ B)
        (hu.inter hA) (hv.union hB) hsub hdis' with hs | hs
    · exact Or.inl (fun x hx => (hs (Or.inl hx)).1)
    · right
      intro x hx
      rcases hs (Or.inl hx) with hxv | hxB
      · exact hxv
      · have hxa : x = a := mem_singleton_iff.mp (hab ▸ ⟨hx, hxB⟩)
        exact hxa ▸ hav
  rcases hcover haA with hau | hav
  · rcases step v u hv hu (by simpa only [union_comm] using hcover)
      (by simpa only [inter_comm u v] using hdis) hau with h | h
    · exact Or.inr h
    · exact Or.inl h
  · exact step u v hu hv hcover hdis hav

/-- A cut point of a compact continuum yields two proper compact continua
meeting exactly at that point. -/
theorem IsConnected.exists_compact_decomposition_of_cut_point
    {S : Set ℂ} (hS : IsConnected S) (hSc : IsCompact S) {a : ℂ} (ha : a ∈ S)
    (hcut : ¬ IsPreconnected (S \ {a})) :
    ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ IsConnected A ∧ IsConnected B ∧
      A ∪ B = S ∧ A ∩ B = {a} ∧ (∃ x ∈ S, x ∉ A) ∧ (∃ y ∈ S, y ∉ B) := by
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAB, hABa, hAp, hBp⟩ :=
    closed_decomposition_of_not_preconnected_sdiff_singleton hSc.isClosed ha hcut
  have hu : IsPreconnected (A ∪ B) := hAB.symm ▸ hS.isPreconnected
  have haAB : a ∈ A ∩ B := hABa.symm ▸ mem_singleton a
  have hA : IsConnected A := ⟨⟨a, haAB.1⟩,
    isPreconnected_left_of_union_inter_singleton hAc hBc hABa hu⟩
  have hB : IsConnected B := ⟨⟨a, haAB.2⟩,
    isPreconnected_left_of_union_inter_singleton hBc hAc
      (by simpa only [inter_comm] using hABa) (by simpa only [union_comm] using hu)⟩
  exact ⟨A, B, hSc.of_isClosed_subset hAc hAs, hSc.of_isClosed_subset hBc hBs,
    hA, hB, hAB, hABa, hAp, hBp⟩

/-- For a connected complementary frontier, a cut point gives two compact
continua that each fail to separate the cluster from the component, while
their union separates them. -/
theorem ae_cluster_cut_point_connected_separation_obstruction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      IsPreconnected (frontier U) →
      ∀ x ∈ cluster (μ ω) 1 z t, ∀ y ∈ U, ∀ a ∈ frontier U,
      ¬ IsPreconnected (frontier U \ {a}) →
      ∃ A B : Set ℂ, IsCompact A ∧ IsCompact B ∧ IsConnected A ∧ IsConnected B ∧
        A ∪ B = frontier U ∧ A ∩ B = {a} ∧
        y ∈ connectedComponentIn Aᶜ x ∧ y ∈ connectedComponentIn Bᶜ x ∧
        y ∉ connectedComponentIn (A ∪ B)ᶜ x := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_cut_point_separation_obstruction hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hω
  intro t ht z hz hcl U hU hfront x hx y hy a ha hcut
  obtain ⟨A, B, hAc, hBc, hAB, hABa, hAx, hBx, hABx⟩ :=
    hω t ht z hz hcl U hU x hx y hy a ha hcut
  have hu : IsPreconnected (A ∪ B) := hAB.symm ▸ hfront
  have haAB : a ∈ A ∩ B := hABa.symm ▸ mem_singleton a
  have hA : IsConnected A := ⟨⟨a, haAB.1⟩,
    isPreconnected_left_of_union_inter_singleton hAc.isClosed hBc.isClosed hABa hu⟩
  have hB : IsConnected B := ⟨⟨a, haAB.2⟩,
    isPreconnected_left_of_union_inter_singleton hBc.isClosed hAc.isClosed
      (by simpa only [inter_comm] using hABa) (by simpa only [union_comm] using hu)⟩
  exact ⟨A, B, hAc, hBc, hA, hB, hAB, hABa, hAx, hBx, hABx⟩

end HarmonicBalls
