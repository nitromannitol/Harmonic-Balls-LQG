import HarmonicBalls.Proofs.Sec11.MassDiameterProbabilitySelection

/-! # Union bound for small tile diameters -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- If the sums of the individual tile failure probabilities tend to zero,
    then the probability that any tile fails also tends to zero. The index
    type may vary with the scale and no event measurability is required. -/
theorem tendsto_all_tiles_failure_of_sum_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (E : ∀ n, ι n → Set Ω)
    (hsum : Tendsto (fun n => ∑ i : ι n, P (E n i)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => P {ω | ∀ i : ι n, ω ∈ E n i}ᶜ) atTop (𝓝 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro n
  calc
    P {ω | ∀ i : ι n, ω ∈ E n i}ᶜ ≤ P (⋃ i : ι n, (E n i)ᶜ) := by
      apply measure_mono
      intro ω hω
      simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hω
      obtain ⟨i, hi⟩ := hω
      exact mem_iUnion.mpr ⟨i, hi⟩
    _ ≤ ∑ i : ι n, P (E n i)ᶜ := measure_iUnion_fintype_le P _

/-- The tile union bound and full support select a mass-carrying class at a
    deterministic scale on which every tile satisfies its good event. -/
theorem exists_mass_scale_class_of_full_support_and_tile_union_bound
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S U : Set X) (C : ℕ → Fin 4 → Set X)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (E : ∀ n, ι n → Set Ω)
    (hAp : 0 < P A) (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set X, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hsum : Tendsto (fun n => ∑ i : ι n, P (E n i)ᶜ) atTop (𝓝 0)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ n j,
      0 < P {ω | ω ∈ A ∧ (∀ i : ι n, ω ∈ E n i) ∧
        (2 : ℝ≥0∞) * c < μ ω (C n j)} := by
  exact exists_mass_scale_class_of_full_support_and_failure_tendsto P μ A S U C
    (fun n => {ω | ∀ i : ι n, ω ∈ E n i}) hAp hU hUne hUS hfull hcover
    (tendsto_all_tiles_failure_of_sum_failure P ι E hsum)

end HarmonicBalls
