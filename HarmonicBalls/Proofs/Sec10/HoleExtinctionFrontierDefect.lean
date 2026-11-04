import HarmonicBalls.Proofs.Sec10.HoleExtinctionMass

/-! # Frontier mass required for the extinction of a hole

If a complementary component disappears, its points lie in the later
closed cluster. The portion not in the later open cluster lies on its
frontier. This gives a mass bound without assuming boundary nullity or
mass saturation at the earlier time.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If a component of the complement of the earlier closed set has no later
descendant, its mass and the mass of the earlier open set are bounded by the
mass of the later open set and its frontier inside the component. -/
theorem measure_add_component_le_of_no_descendant
    (μ : Measure ℂ) {C D U : Set ℂ}
    (hC : MeasurableSet C) (hD : IsOpen D) (hCD : C ⊆ D)
    (hU : U ∈ connectedComponentsIn (closure C)ᶜ)
    (hno : ¬ ∃ V ∈ connectedComponentsIn (closure D)ᶜ, V ⊆ U) :
    μ C + μ U ≤ μ D + μ (frontier D ∩ U) := by
  have hcover := complement_component_subset_of_no_descendant (closure_mono hCD) hU hno
  have hUsub : U ⊆ (closure C)ᶜ := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint C U := disjoint_left.mpr (fun x hx hxU =>
    hUsub hxU (subset_closure hx))
  have hsub : C ∪ U ⊆ D ∪ (frontier D ∩ U) := by
    intro x hx
    rcases hx with hxC | hxU
    · exact Or.inl (hCD hxC)
    · by_cases hxD : x ∈ D
      · exact Or.inl hxD
      · right
        refine ⟨?_, hxU⟩
        rw [hD.frontier_eq]
        exact ⟨hcover hxU, hxD⟩
  calc
    μ C + μ U = μ (C ∪ U) := (measure_union' hdis hC).symm
    _ ≤ μ (D ∪ (frontier D ∩ U)) := measure_mono hsub
    _ ≤ μ D + μ (frontier D ∩ U) := measure_union_le _ _

universe u

/-- On the I2 event, a component that has disappeared by time `s` must fit
within the later mass budget after adding its mass and the earlier cluster
mass, up to the later frontier mass inside the component. All radii,
centres, times and components are simultaneous. -/
theorem ae_cluster_component_mass_le_later_mass_add_frontier_of_no_descendant
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t s : ℝ, 0 < R → 0 < t → t ≤ s →
      ∀ z ∈ ball (0 : ℂ) R,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) R z t))ᶜ,
      (¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) R z s))ᶜ, V ⊆ U) →
      μ ω (cluster (μ ω) R z t) + μ ω U ≤
        ENNReal.ofReal s + μ ω (frontier (cluster (μ ω) R z s) ∩ U) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hopen hmono hmass
  intro R t s hR ht hts z hz U hU hno
  have hs : 0 < s := ht.trans_le hts
  exact (measure_add_component_le_of_no_descendant (μ ω)
    (hopen t R ht hR z hz).1.measurableSet (hopen s R hs hR z hz).1
    (hmono t s R ht hts hR z hz) hU hno).trans
    (add_le_add (hmass R s hR hs z hz).1 le_rfl)

/-- If the combined mass of the earlier cluster and its complementary
component exceeds the later time, then either the component has a descendant
or the later frontier inside it has positive mass. -/
theorem ae_cluster_component_descendant_or_positive_frontier_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t s : ℝ, 0 < R → 0 < t → t ≤ s →
      ∀ z ∈ ball (0 : ℂ) R,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) R z t))ᶜ,
      ENNReal.ofReal s < μ ω (cluster (μ ω) R z t) + μ ω U →
      (∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) R z s))ᶜ, V ⊆ U) ∨
      0 < μ ω (frontier (cluster (μ ω) R z s) ∩ U) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_component_mass_le_later_mass_add_frontier_of_no_descendant hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hbound
  intro R t s hR ht hts z hz U hU hlarge
  by_cases hdesc : ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) R z s))ᶜ, V ⊆ U
  · exact Or.inl hdesc
  · right
    by_contra hn
    have hz' : μ ω (frontier (cluster (μ ω) R z s) ∩ U) = 0 :=
      le_antisymm (not_lt.mp hn) bot_le
    have hb := hbound R t s hR ht hts z hz U hU hdesc
    rw [hz', add_zero] at hb
    exact (not_le_of_gt hlarge) hb

end HarmonicBalls
