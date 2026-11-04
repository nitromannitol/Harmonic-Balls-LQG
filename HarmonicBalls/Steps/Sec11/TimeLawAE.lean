import HarmonicBalls.Steps.Sec11.TimeDistributionAE

/-! # The first-entry-time pushforward law -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- An increasing open family covering almost every point and having mass `t` has
Lebesgue measure on positive times as its first-entry-time pushforward. -/
theorem map_positive_entry_time_eq_volume_of_ae_cover
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (Λ : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hcover : ∀ᵐ x ∂μ, ∃ t, 0 < t ∧ x ∈ Λ t)
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hmass : ∀ t, 0 < t → μ (Λ t) = ENNReal.ofReal t) :
    μ.map (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) = volume.restrict (Ioi (0 : ℝ)) := by
  let τ : X → ℝ := fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}
  have hτ : Measurable τ := measurable_positive_entry_time_without_cover Λ hopen
  have hIio : ∀ a : ℝ, μ.map τ (Iio a) = (volume.restrict (Ioi (0 : ℝ))) (Iio a) := by
    intro a
    rw [Measure.map_apply hτ measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
    have hset : Iio a ∩ Ioi (0 : ℝ) = Ioo 0 a := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
    rw [hset, Real.volume_Ioo, sub_zero]
    by_cases ha : 0 < a
    · exact measure_positive_entry_time_preimage_Iio_of_ae_cover μ Λ hcover hmono hmass a ha
    · have hempty : τ ⁻¹' Iio a = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hzero : 0 ≤ τ x := by
          dsimp only [τ]
          by_cases hx : ∃ t : ℝ, 0 < t ∧ x ∈ Λ t
          · exact le_csInf hx (fun _ ht => ht.1.le)
          · have he : {t : ℝ | 0 < t ∧ x ∈ Λ t} = ∅ :=
              Set.eq_empty_iff_forall_notMem.mpr (fun t ht => hx ⟨t, ht⟩)
            simp [he]
        exact not_lt_of_ge (le_trans (le_of_not_gt ha) hzero) hx
      rw [hempty, measure_empty, ENNReal.ofReal_eq_zero.mpr (le_of_not_gt ha)]
  apply Measure.ext_of_generateFrom_of_iUnion (range Iio)
    (fun n : ℕ => Iio ((n : ℝ) + 1))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio
  · apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, by simp only [mem_Iio]; linarith⟩
  · intro n
    exact ⟨(n : ℝ) + 1, rfl⟩
  · intro n
    rw [hIio]
    rw [Measure.restrict_apply measurableSet_Iio]
    have hset : Iio ((n : ℝ) + 1) ∩ Ioi (0 : ℝ) = Ioo 0 ((n : ℝ) + 1) := by
      ext x
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]
    rw [hset, Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_ne_top
  · rintro _ ⟨a, rfl⟩
    exact hIio a

/-- For a point which enters, right-continuity of closures places it in the
closure at its positive first-entry time. -/
theorem mem_closure_at_positive_entry_of_mem_some
    {X : Type*} [TopologicalSpace X] (Λ : ℝ → Set X)
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hright : ∀ t, 0 < t → closure (Λ t) = ⋂ s ∈ Ioi t, closure (Λ s))
    (x : X) (hx : ∃ t, 0 < t ∧ x ∈ Λ t)
    (hpos : 0 < sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) :
    x ∈ closure (Λ (sInf {t : ℝ | 0 < t ∧ x ∈ Λ t})) := by
  rw [hright _ hpos]
  simp only [mem_iInter, mem_Ioi]
  intro s hs
  obtain ⟨t, ⟨ht, hxt⟩, hts⟩ :=
    (csInf_lt_iff (s := {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⟨0, fun _ ht => ht.1.le⟩ hx).1 hs
  exact subset_closure (hmono ht (lt_trans hpos hs) hts.le hxt)

/-- Under almost-everywhere exhaustion, mass parametrization and
right-continuity of closures put almost every point on its entry frontier. -/
theorem ae_mem_frontier_at_positive_entry_of_ae_cover
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (Λ : ℝ → Set X) (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hcover : ∀ᵐ x ∂μ, ∃ t, 0 < t ∧ x ∈ Λ t)
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hmass : ∀ t, 0 < t → μ (Λ t) = ENNReal.ofReal t)
    (hright : ∀ t, 0 < t → closure (Λ t) = ⋂ s ∈ Ioi t, closure (Λ s)) :
    ∀ᵐ x ∂μ, 0 < sInf {t : ℝ | 0 < t ∧ x ∈ Λ t} →
      x ∈ frontier (Λ (sInf {t : ℝ | 0 < t ∧ x ∈ Λ t})) := by
  let τ : X → ℝ := fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}
  have hτ : Measurable τ := measurable_positive_entry_time_without_cover Λ hopen
  have hmap : μ.map τ = volume.restrict (Ioi (0 : ℝ)) :=
    map_positive_entry_time_eq_volume_of_ae_cover μ Λ hopen hcover hmono hmass
  have : NullSingletonClass (μ.map τ) := by rw [hmap]; infer_instance
  refine ae_mem_frontier_at_first_entry μ Λ τ hopen ?_ hτ.aemeasurable ?_
  · exact fun x t ht hlt => not_mem_before_positive_entry Λ x t ht hlt
  · filter_upwards [hcover] with x hx hpos
    exact mem_closure_at_positive_entry_of_mem_some Λ hmono hright x hx hpos

end HarmonicBalls
