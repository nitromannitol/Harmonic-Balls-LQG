import Mathlib

/-! # First-entry times of increasing open families

A countable basis shows that points entering an open family exactly at their
first positive entry time can only enter at countably many times. This is a
step in the time-to-boundary reduction used in Section 11.
-/

namespace HarmonicBalls

open MeasureTheory Set Topology

/-- For an open family and a first-entry function, the times at which a point
belongs to the open set at its own first entry time form a countable set.
No measurability of that set is assumed. -/
theorem countable_times_of_mem_at_first_entry
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    (Λ : ℝ → Set X) (τ : X → ℝ)
    (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hfirst : ∀ x t, 0 < t → t < τ x → x ∉ Λ t) :
    {t : ℝ | ∃ x, 0 < τ x ∧ τ x = t ∧ x ∈ Λ (τ x)}.Countable := by
  let entry : Set X → ℝ := fun B => sInf {t : ℝ | 0 < t ∧ B ⊆ Λ t}
  apply ((TopologicalSpace.countable_countableBasis X).image entry).mono
  rintro t ⟨x, hτ, rfl, hx⟩
  obtain ⟨B, hB, hxB, hBsub⟩ :=
    (TopologicalSpace.isBasis_countableBasis X).mem_nhds_iff.mp ((hopen (τ x) hτ).mem_nhds hx)
  refine ⟨B, hB, ?_⟩
  dsimp only [entry]
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ ht => ht.1.le⟩ ⟨hτ, hBsub⟩
  · refine le_csInf ?_ ?_
    · exact ⟨τ x, hτ, hBsub⟩
    intro s hs
    apply le_of_not_gt
    intro hlt
    exact hfirst x s hs.1 hlt (hs.2 hxB)

/-- If first-entry times have an atomless distribution, almost every point is
outside the open set at its own positive first-entry time. -/
theorem ae_not_mem_at_first_entry
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    (μ : Measure X) (Λ : ℝ → Set X) (τ : X → ℝ)
    (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hfirst : ∀ x t, 0 < t → t < τ x → x ∉ Λ t)
    (hτ : AEMeasurable τ μ) [NullSingletonClass (μ.map τ)] :
    ∀ᵐ x ∂μ, 0 < τ x → x ∉ Λ (τ x) := by
  let E : Set ℝ := {t | ∃ x, 0 < τ x ∧ τ x = t ∧ x ∈ Λ (τ x)}
  have hE : E.Countable := countable_times_of_mem_at_first_entry Λ τ hopen hfirst
  have hnull : μ (τ ⁻¹' E) = 0 := Measure.preimage_null_of_map_null hτ (hE.measure_zero _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hpos hmem
  exact hx ⟨x, hpos, rfl, hmem⟩

/-- The infimum of the positive entry times satisfies the first-entry
property, including when the point never enters the family. -/
theorem not_mem_before_positive_entry {X : Type*} (Λ : ℝ → Set X) (x : X) (t : ℝ)
    (ht : 0 < t) (hlt : t < sInf {s : ℝ | 0 < s ∧ x ∈ Λ s}) : x ∉ Λ t := by
  intro hx
  have hle : sInf {s : ℝ | 0 < s ∧ x ∈ Λ s} ≤ t :=
    csInf_le ⟨0, fun _ hs => hs.1.le⟩ ⟨ht, hx⟩
  exact (not_lt_of_ge hle) hlt

/-- If a point lies in the closure at its first entry time, then under an
atomless entry-time distribution it lies on the frontier almost surely. -/
theorem ae_mem_frontier_at_first_entry
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    (μ : Measure X) (Λ : ℝ → Set X) (τ : X → ℝ)
    (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hfirst : ∀ x t, 0 < t → t < τ x → x ∉ Λ t)
    (hτ : AEMeasurable τ μ) [NullSingletonClass (μ.map τ)]
    (hclosure : ∀ᵐ x ∂μ, 0 < τ x → x ∈ closure (Λ (τ x))) :
    ∀ᵐ x ∂μ, 0 < τ x → x ∈ frontier (Λ (τ x)) := by
  filter_upwards [ae_not_mem_at_first_entry μ Λ τ hopen hfirst hτ, hclosure] with x hnot hcl hpos
  rw [frontier, (hopen (τ x) hpos).interior_eq]
  exact ⟨hcl hpos, hnot hpos⟩

/-- Strict sublevel sets of the positive first-entry time are unions of the
open family, provided every point eventually enters. -/
theorem positive_entry_time_preimage_Iio
    {X : Type*} (Λ : ℝ → Set X) (hcover : ∀ x, ∃ t, 0 < t ∧ x ∈ Λ t) (a : ℝ) :
    (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⁻¹' Iio a =
      ⋃ t ∈ Ioo (0 : ℝ) a, Λ t := by
  ext x
  simp only [mem_preimage, mem_Iio, mem_iUnion, mem_Ioo]
  rw [csInf_lt_iff (s := {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⟨0, fun _ ht => ht.1.le⟩ (hcover x)]
  constructor
  · rintro ⟨t, ⟨ht, hx⟩, ha⟩
    exact ⟨t, ⟨ht, ha⟩, hx⟩
  · rintro ⟨t, ⟨ht, ha⟩, hx⟩
    exact ⟨t, ⟨ht, hx⟩, ha⟩

/-- If the open family covers the space, the infimum of the positive entry
times is measurable. -/
theorem measurable_positive_entry_time
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (Λ : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hcover : ∀ x, ∃ t, 0 < t ∧ x ∈ Λ t) :
    Measurable (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) := by
  apply measurable_of_Iio
  intro a
  rw [positive_entry_time_preimage_Iio Λ hcover a]
  exact (isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht.1).measurableSet

end HarmonicBalls
