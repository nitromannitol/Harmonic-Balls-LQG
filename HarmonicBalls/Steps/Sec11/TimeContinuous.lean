import HarmonicBalls.Steps.Sec11.TimeLawAE

/-! # Continuity of the entry time away from rational-time frontiers -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- At a point of positive entry time which lies on no rational-time frontier,
the first-entry-time function is continuous. -/
theorem continuousAt_positive_entry_time
    {X : Type*} [TopologicalSpace X] (Λ : ℝ → Set X)
    (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (x : X) (hx : ∃ t, 0 < t ∧ x ∈ Λ t)
    (hpos : 0 < sInf {t : ℝ | 0 < t ∧ x ∈ Λ t})
    (havoid : ∀ q : ℚ, 0 < (q : ℝ) → x ∉ frontier (Λ q)) :
    ContinuousAt (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) x := by
  let τ : X → ℝ := fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}
  let U : Set X := ⋃ t ∈ Ioi (0 : ℝ), Λ t
  have hU : IsOpen U := isOpen_iUnion fun t => isOpen_iUnion fun ht => hopen t ht
  have hxU : x ∈ U := by
    obtain ⟨t, ht, hxt⟩ := hx
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hxt⟩⟩
  change Tendsto τ (𝓝 x) (𝓝 (τ x))
  apply tendsto_order.2
  constructor
  · intro a ha
    have hp : max a 0 < τ x := max_lt ha hpos
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hp
    have hqpos : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hqlo
    have hqbelow : a < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hqlo
    have hnot : x ∉ Λ q := not_mem_before_positive_entry Λ x q hqpos hqhi
    have hnotcl : x ∉ closure (Λ q) := by
      intro hc
      apply havoid q hqpos
      rw [frontier, (hopen q hqpos).interior_eq]
      exact ⟨hc, hnot⟩
    filter_upwards [hU.mem_nhds hxU, isClosed_closure.isOpen_compl.mem_nhds hnotcl] with y hyU hycl
    have hy : ∃ t, 0 < t ∧ y ∈ Λ t := by
      simp only [U, mem_iUnion, mem_Ioi] at hyU
      obtain ⟨t, ht, hyt⟩ := hyU
      exact ⟨t, ht, hyt⟩
    have hle : (q : ℝ) ≤ τ y := by
      apply le_csInf hy
      intro s hs
      by_contra hn
      have hsq : s ≤ (q : ℝ) := (lt_of_not_ge hn).le
      exact hycl (subset_closure (hmono hs.1 hqpos hsq hs.2))
    exact lt_of_lt_of_le hqbelow hle
  · intro a ha
    obtain ⟨s, ⟨hs, hxs⟩, hsa⟩ :=
      (csInf_lt_iff (s := {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⟨0, fun _ ht => ht.1.le⟩ hx).1 ha
    filter_upwards [(hopen s hs).mem_nhds hxs] with y hys
    have hle : τ y ≤ s := csInf_le ⟨0, fun _ ht => ht.1.le⟩ ⟨hs, hys⟩
    exact lt_of_le_of_lt hle hsa

/-- Under the mass parametrization and zero frontier mass, the first-entry
time is continuous almost everywhere. -/
theorem ae_continuousAt_positive_entry_time
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (Λ : ℝ → Set X)
    (hopen : ∀ t, 0 < t → IsOpen (Λ t))
    (hcover : ∀ᵐ x ∂μ, ∃ t, 0 < t ∧ x ∈ Λ t)
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hmass : ∀ t, 0 < t → μ (Λ t) = ENNReal.ofReal t)
    (hfrontier : ∀ t, 0 < t → μ (frontier (Λ t)) = 0) :
    ∀ᵐ x ∂μ, ContinuousAt (fun y => sInf {t : ℝ | 0 < t ∧ y ∈ Λ t}) x := by
  let τ : X → ℝ := fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}
  have hτ : Measurable τ := measurable_positive_entry_time_without_cover Λ hopen
  have hmap : μ.map τ = volume.restrict (Ioi (0 : ℝ)) :=
    map_positive_entry_time_eq_volume_of_ae_cover μ Λ hopen hcover hmono hmass
  have hpos : ∀ᵐ x ∂μ, 0 < τ x := by
    apply (ae_map_iff hτ.aemeasurable measurableSet_Ioi).1
    rw [hmap]
    exact ae_restrict_mem measurableSet_Ioi
  have havoid : ∀ᵐ x ∂μ, ∀ q : ℚ, 0 < (q : ℝ) → x ∉ frontier (Λ q) := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hfrontier q hq)] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun _ h => False.elim (hq h)
  filter_upwards [hcover, hpos, havoid] with x hx hp hq
  exact continuousAt_positive_entry_time Λ hopen hmono x hx hp hq

end HarmonicBalls
