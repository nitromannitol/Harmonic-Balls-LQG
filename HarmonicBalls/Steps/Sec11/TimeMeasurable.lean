import HarmonicBalls.Steps.Sec11.TimeEntry

/-! # Measurability of positive first-entry times -/

namespace HarmonicBalls

open MeasureTheory Set Topology

/-- The positive first-entry time is measurable even if some points never
enter: their infimum is zero. -/
theorem measurable_positive_entry_time_without_cover
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (Λ : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (Λ t)) :
    Measurable (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) := by
  let U : Set X := ⋃ t ∈ Ioi (0 : ℝ), Λ t
  have hU : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht
  apply measurable_of_Iio
  intro a
  by_cases ha : 0 < a
  · have heq : (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⁻¹' Iio a =
        Uᶜ ∪ ⋃ t ∈ Ioo (0 : ℝ) a, Λ t := by
      ext x
      simp only [mem_preimage, mem_Iio, mem_union, mem_compl_iff, U, mem_iUnion,
        mem_Ioi, mem_Ioo]
      by_cases hx : ∃ t : ℝ, 0 < t ∧ x ∈ Λ t
      · have hi : sInf {t : ℝ | 0 < t ∧ x ∈ Λ t} < a ↔
          ∃ t ∈ {t : ℝ | 0 < t ∧ x ∈ Λ t}, t < a :=
          csInf_lt_iff (s := {t : ℝ | 0 < t ∧ x ∈ Λ t})
          ⟨0, fun _ ht => ht.1.le⟩ hx
        simp only [not_exists]
        constructor
        · intro h
          obtain ⟨t, ⟨ht, hxt⟩, hta⟩ := hi.mp h
          exact Or.inr ⟨t, ⟨ht, hta⟩, hxt⟩
        · rintro (h | ⟨t, ⟨ht, hta⟩, hxt⟩)
          · obtain ⟨t, ht, hxt⟩ := hx
            exact False.elim (h t ht hxt)
          · exact hi.mpr ⟨t, ⟨ht, hxt⟩, hta⟩
      · have hempty : {t : ℝ | 0 < t ∧ x ∈ Λ t} = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun t ht => hx ⟨t, ht⟩)
        simp only [hempty, Real.sInf_empty, ha, true_iff]
        exact Or.inl (by simpa only [not_exists, not_and] using hx)
    rw [heq]
    exact hU.measurableSet.compl.union
      (isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht.1).measurableSet
  · have hempty : (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⁻¹' Iio a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hnonneg : 0 ≤ sInf {t : ℝ | 0 < t ∧ x ∈ Λ t} := by
        by_cases h : ∃ t : ℝ, 0 < t ∧ x ∈ Λ t
        · exact le_csInf h (fun _ ht => ht.1.le)
        · have he : {t : ℝ | 0 < t ∧ x ∈ Λ t} = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun t ht => h ⟨t, ht⟩)
          simp [he]
      exact not_lt_of_ge (le_trans (le_of_not_gt ha) hnonneg) hx
    rw [hempty]
    exact MeasurableSet.empty

end HarmonicBalls
