import HarmonicBalls.Proofs.Counterexamples.Prop10_6
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-!
# Components of the complement of a connected closed set

The proof of Proposition 10.6 applies Lemma 10.5 to each complementary
component. Its hypothesis that the component has connected complement follows
from these general facts for locally connected, connected ambient spaces.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The frontier of a component of an open set lies in the frontier of the
open set. -/
theorem frontier_connectedComponentIn_subset_frontier
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {F : Set X} (hF : IsOpen F) (p : X) :
    frontier (connectedComponentIn F p) ⊆ frontier F := by
  intro x hx
  have hUopen : IsOpen (connectedComponentIn F p) := hF.connectedComponentIn
  rw [hUopen.frontier_eq] at hx
  rw [hF.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset F p) hx.1, ?_⟩
  intro hxF
  exact hx.2 (mem_connectedComponentIn_of_mem_closure hF hxF hx.1)

/-- In a connected, locally connected ambient space, each component of the
complement of a nonempty closed set has closure meeting the set. -/
theorem closure_component_compl_inter_nonempty
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hK : IsClosed K) (hne : K.Nonempty) {p : X} (hp : p ∈ Kᶜ) :
    (closure (connectedComponentIn Kᶜ p) ∩ K).Nonempty := by
  classical
  let V := connectedComponentIn Kᶜ p
  have hVo : IsOpen V := hK.isOpen_compl.connectedComponentIn
  have hpV : p ∈ V := mem_connectedComponentIn hp
  by_contra h
  have hclF : closure V ⊆ Kᶜ := by
    intro x hx hxK
    exact h ⟨x, hx, hxK⟩
  have hclV : closure V ⊆ V := by
    intro x hx
    exact mem_connectedComponentIn_of_mem_closure hK.isOpen_compl (hclF hx) hx
  have hVc : IsClosed V := closure_subset_iff_isClosed.mp hclV
  have hVu : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ ⟨p, hpV⟩
  obtain ⟨x, hx⟩ := hne
  have hxV : x ∈ V := by rw [hVu]; trivial
  exact (connectedComponentIn_subset Kᶜ p hxV) hx

/-- The complement of a component of the complement of a nonempty connected
closed set is connected. -/
theorem isConnected_compl_component_compl
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {K : Set X} (hKc : IsClosed K) (hK : IsConnected K) {p : X} :
    IsConnected (connectedComponentIn Kᶜ p)ᶜ := by
  classical
  let U := connectedComponentIn Kᶜ p
  have hUo : IsOpen U := hKc.isOpen_compl.connectedComponentIn
  have hUK : K ⊆ Uᶜ := by
    intro x hxK hxU
    exact (connectedComponentIn_subset Kᶜ p hxU) hxK
  obtain ⟨a, ha⟩ := hK.nonempty
  refine ⟨⟨a, hUK ha⟩, isPreconnected_of_forall a ?_⟩
  intro y hy
  by_cases hyK : y ∈ K
  · exact ⟨K, hUK, ha, hyK, hK.isPreconnected⟩
  · let V := connectedComponentIn Kᶜ y
    have hyF : y ∈ Kᶜ := hyK
    have hyV : y ∈ V := mem_connectedComponentIn hyF
    have hVU : V ⊆ Uᶜ := by
      intro x hxV hxU
      have e₁ : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ x :=
        connectedComponentIn_eq hxV
      have e₂ : connectedComponentIn Kᶜ p = connectedComponentIn Kᶜ x :=
        connectedComponentIn_eq hxU
      have : y ∈ U := by
        change y ∈ connectedComponentIn Kᶜ p
        rw [e₂, ← e₁]
        exact hyV
      exact hy this
    have hclVU : closure V ⊆ Uᶜ := closure_minimal hVU hUo.isClosed_compl
    have hmeet : (K ∩ closure V).Nonempty := by
      obtain ⟨x, hxV, hxK⟩ := closure_component_compl_inter_nonempty hKc hK.nonempty hyF
      exact ⟨x, hxK, hxV⟩
    refine ⟨K ∪ closure V, union_subset hUK hclVU, Or.inl ha,
      Or.inr (subset_closure hyV), ?_⟩
    exact hK.isPreconnected.union' hmeet isPreconnected_connectedComponentIn.closure

/-- On the event of cluster openness and connectedness, the complementary
components have the topological hypotheses used in Lemma 10.5. -/
theorem clusterComplementComponent_geometry
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ)
    (hcluster : ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
      IsOpen (cluster (μ ω) r z t) ∧ IsConnected (cluster (μ ω) r z t)) :
    ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
      closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) r z t))ᶜ,
        IsOpen U ∧ IsConnected U ∧ IsConnected Uᶜ ∧
        frontier U ⊆ frontier (cluster (μ ω) r z t) ∧
        closure (frontier U) ⊆ ball 0 r := by
  filter_upwards [hcluster] with ω hω
  intro t r ht hr z hz hcl U hU
  obtain ⟨p, hp, rfl⟩ := hU
  let K := closure (cluster (μ ω) r z t)
  let V := connectedComponentIn Kᶜ p
  have hG := hω t r ht hr z hz
  have hKo : IsOpen Kᶜ := isClosed_closure.isOpen_compl
  have hVo : IsOpen V := hKo.connectedComponentIn
  have hVK : V ⊆ Kᶜ := connectedComponentIn_subset Kᶜ p
  have hfrK : frontier V ⊆ K := by
    intro x hx
    have hfront := frontier_connectedComponentIn_subset_frontier hKo p hx
    rw [hKo.frontier_eq] at hfront
    exact not_not.mp hfront.2
  have hVG : Disjoint V (cluster (μ ω) r z t) := by
    rw [Set.disjoint_left]
    intro x hxV hxG
    exact hVK hxV (subset_closure hxG)
  have hfrG : frontier V ⊆ frontier (cluster (μ ω) r z t) := by
    intro x hx
    rw [hG.1.frontier_eq]
    refine ⟨hfrK hx, ?_⟩
    exact (Set.disjoint_left.mp (hVG.closure_left hG.1)) (frontier_subset_closure hx)
  refine ⟨hVo, isConnected_connectedComponentIn_iff.mpr hp,
    isConnected_compl_component_compl isClosed_closure hG.2.closure,
    hfrG, ?_⟩
  exact (closure_minimal hfrK isClosed_closure).trans hcl

universe u

/-- The complementary-component geometry follows on the volume-growth event. -/
theorem clusterComplementComponent_geometry_of_volumeGrowth
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
      closure (cluster (μ ω) r z t) ⊆ ball 0 r →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) r z t))ᶜ,
        IsOpen U ∧ IsConnected U ∧ IsConnected Uᶜ ∧
        frontier U ⊆ frontier (cluster (μ ω) r z t) ∧
        closure (frontier U) ⊆ ball 0 r := by
  apply clusterComplementComponent_geometry P μ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro t r ht hr z hz
  exact ⟨(hω t r ht hr z hz).1, (hω t r ht hr z hz).2.1⟩

end HarmonicBalls
