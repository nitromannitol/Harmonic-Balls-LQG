import HarmonicBalls.Proofs.Sec10.LocalFrontierLength
import HarmonicBalls.Proofs.Sec10.CutPointCharacterization

/-! # Dimension of essential pieces of a complementary frontier

Every relatively open nonempty part of a common frontier has Hausdorff
 dimension at least one. This constrains closed decompositions of the frontier.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- If every nonempty ball centered on `S` meets `S` in a set of Hausdorff
 dimension at least one, then a proper closed cover by two sets has essential
 parts of dimension at least one. -/
theorem closed_cover_essential_parts_dimH
    {S A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = S)
    (hproperA : ∃ x ∈ S, x ∉ A) (hproperB : ∃ x ∈ S, x ∉ B)
    (hlocal : ∀ p ∈ S, ∀ r : ℝ, 0 < r → 1 ≤ dimH (S ∩ ball p r)) :
    1 ≤ dimH (A \ B) ∧ 1 ≤ dimH (B \ A) := by
  constructor
  · obtain ⟨p, hpS, hpB⟩ := hproperB
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hpB)
    apply (hlocal p hpS r hr).trans
    apply dimH_mono
    intro q hq
    have hqB : q ∉ B := hball hq.2
    have hqAB : q ∈ A ∪ B := hcover.symm ▸ hq.1
    exact ⟨hqAB.resolve_right hqB, hqB⟩
  · obtain ⟨p, hpS, hpA⟩ := hproperA
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hA.isOpen_compl.mem_nhds hpA)
    apply (hlocal p hpS r hr).trans
    apply dimH_mono
    intro q hq
    have hqA : q ∉ A := hball hq.2
    have hqAB : q ∈ A ∪ B := hcover.symm ▸ hq.1
    exact ⟨hqAB.resolve_left hqA, hqA⟩

/-- Neither essential part of such a cover can be countable. -/
theorem closed_cover_essential_parts_uncountable
    {S A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = S)
    (hproperA : ∃ x ∈ S, x ∉ A) (hproperB : ∃ x ∈ S, x ∉ B)
    (hlocal : ∀ p ∈ S, ∀ r : ℝ, 0 < r → 1 ≤ dimH (S ∩ ball p r)) :
    ¬ (A \ B).Countable ∧ ¬ (B \ A).Countable := by
  obtain ⟨hAB, hBA⟩ :=
    closed_cover_essential_parts_dimH hA hB hcover hproperA hproperB hlocal
  constructor
  · intro h
    rw [h.dimH_zero] at hAB
    exact one_ne_zero (le_antisymm hAB zero_le_one)
  · intro h
    rw [h.dimH_zero] at hBA
    exact one_ne_zero (le_antisymm hBA zero_le_one)

/-- A cut point of a common frontier yields two closed nonseparating pieces,
each of whose essential parts has Hausdorff dimension at least one. -/
theorem cut_point_yields_nonseparating_pieces_dimH
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {x y a : ℂ}
    (hx : x ∈ G) (hy : y ∈ U) (ha : a ∈ frontier U)
    (hcut : ¬ IsPreconnected (frontier U \ {a}))
    (hlocal : ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r →
      1 ≤ dimH (frontier U ∩ ball p r)) :
    ∃ A B : Set ℂ, IsClosed A ∧ IsClosed B ∧ A ∪ B = frontier U ∧
      A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
      y ∈ connectedComponentIn Bᶜ x ∧
      1 ≤ dimH (A \ B) ∧ 1 ≤ dimH (B \ A) := by
  obtain ⟨A, B, hA, hB, hAB, hab, hAx, hBx⟩ :=
    (cut_point_iff_nonseparating_frontier_decomposition
      hGo hGc hUo hUc hdis hfront hx hy ha).mp hcut
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
  obtain ⟨hAd, hBd⟩ := closed_cover_essential_parts_dimH hA hB hAB hAp hBp hlocal
  exact ⟨A, B, hA, hB, hAB, hab, hAx, hBx, hAd, hBd⟩

universe u

/-- Under volume growth, both essential parts of any proper closed two-set
cover of any compact-cluster complementary frontier have Hausdorff dimension
at least one. -/
theorem ae_cluster_frontier_closed_cover_essential_parts_dimH
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ A B : Set ℂ, IsClosed A → IsClosed B → A ∪ B = frontier U →
      (∃ x ∈ frontier U, x ∉ A) → (∃ x ∈ frontier U, x ∉ B) →
      1 ≤ dimH (A \ B) ∧ 1 ≤ dimH (B \ A) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_complement_frontier_local_dimH hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hlocal
  intro t ht z hz hcl U hU A B hA hB hcover hproperA hproperB
  exact closed_cover_essential_parts_dimH hA hB hcover hproperA hproperB
    (hlocal t ht z hz hcl U hU)

/-- Under volume growth, every cut point of every compact-cluster
complementary frontier admits a nonseparating closed decomposition with
both essential parts of Hausdorff dimension at least one. -/
theorem ae_cluster_cut_point_yields_nonseparating_pieces_dimH
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
      ∃ A B : Set ℂ, IsClosed A ∧ IsClosed B ∧ A ∪ B = frontier U ∧
        A ∩ B = {a} ∧ y ∈ connectedComponentIn Aᶜ x ∧
        y ∈ connectedComponentIn Bᶜ x ∧
        1 ≤ dimH (A \ B) ∧ 1 ≤ dimH (B \ A) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_complement_frontier_local_dimH hI2 γ hγ hγ2 α₀ hα
      Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster hlocal
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
  exact cut_point_yields_nonseparating_pieces_dimH hc.1 hc.2.1 hg.1 hg.2.1 hdis
    hg.2.2.2.1 hx hy ha hcut (hlocal t ht z hz hcl U ⟨v, hv, hUeq⟩)

end HarmonicBalls
