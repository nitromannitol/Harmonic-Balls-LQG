import Mathlib

/-!
# Countable π-system for the Borel sets of `ℂ` (fp-S11s-11-13-B1-covariance, step B2)

Two Radon measures on `ℂ` that agree on a countable π-system `C` generating the Borel sets are equal, once `C`
contains an exhausting sequence of sets of compact closure (`measure_ext_of_complex_pi`). The π-system used is
the family of finite intersections of a countable basis of `ℂ`, which is countable (`exists_countable_pi_system_complex`).
This is the countable determining family of the covariance event (ruling section 3, part B).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A countable π-system generating the Borel sets of `ℂ`, with an exhausting sequence `B n ∈ C` of sets of
compact closure. -/
theorem exists_countable_pi_system_complex :
    ∃ C : Set (Set ℂ), C.Countable ∧ IsPiSystem C ∧ MeasurableSpace.generateFrom C = borel ℂ ∧
      ∃ B : ℕ → Set ℂ, (∀ n, B n ∈ C) ∧ (⋃ n, B n = univ) ∧ ∀ n, IsCompact (closure (B n)) := by
  obtain ⟨Bs, hBs, -, hbas⟩ := TopologicalSpace.exists_countable_basis ℂ
  let C : Set (Set ℂ) := (fun t : Set (Set ℂ) => ⋂₀ t) '' {t | t.Finite ∧ t ⊆ Bs}
  have hCc : C.Countable := (Set.countable_ofPred_finite_subset hBs).image _
  have hpi : IsPiSystem C := by
    intro s hs t ht _
    obtain ⟨F, ⟨hFf, hFs⟩, rfl⟩ := hs
    obtain ⟨G, ⟨hGf, hGs⟩, rfl⟩ := ht
    exact ⟨F ∪ G, ⟨hFf.union hGf, union_subset hFs hGs⟩, sInter_union F G⟩
  have hgen : MeasurableSpace.generateFrom C = borel ℂ := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      rintro _ ⟨F, ⟨hFf, hFs⟩, rfl⟩
      exact (hFf.isOpen_sInter (fun s hs => hbas.isOpen (hFs hs))).measurableSet
    · rw [hbas.borel_eq_generateFrom]
      apply MeasurableSpace.generateFrom_mono
      intro s hs
      exact ⟨{s}, ⟨Set.finite_singleton s, singleton_subset_iff.2 hs⟩, sInter_singleton s⟩
  have hcov : ∀ z : ℂ, ∃ b ∈ {b | b ∈ Bs ∧ IsCompact (closure b)}, z ∈ b := by
    intro z
    obtain ⟨b, hbBs, hzb, hbsub⟩ := hbas.mem_nhds_iff.1 (Metric.ball_mem_nhds z one_pos)
    refine ⟨b, ⟨hbBs, ?_⟩, hzb⟩
    exact (isCompact_closedBall z 1).of_isClosed_subset isClosed_closure
      (closure_minimal (hbsub.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall)
  have hBc_count : {b | b ∈ Bs ∧ IsCompact (closure b)}.Countable := hBs.mono (fun b hb => hb.1)
  have hBc_ne : {b | b ∈ Bs ∧ IsCompact (closure b)}.Nonempty :=
    (hcov 0).elim fun b hb => ⟨b, hb.1⟩
  obtain ⟨B, hB⟩ := hBc_count.exists_eq_range hBc_ne
  have hmemB : ∀ n, B n ∈ {b | b ∈ Bs ∧ IsCompact (closure b)} := fun n => by
    rw [hB]
    exact mem_range_self n
  refine ⟨C, hCc, hpi, hgen, B, fun n => ⟨{B n}, ⟨Set.finite_singleton _, singleton_subset_iff.2 (hmemB n).1⟩,
    sInter_singleton _⟩, ?_, fun n => (hmemB n).2⟩
  apply eq_univ_of_forall
  intro z
  obtain ⟨b, hb, hzb⟩ := hcov z
  rw [hB] at hb
  obtain ⟨n, rfl⟩ := hb
  exact mem_iUnion.2 ⟨n, hzb⟩

/-- **Uniqueness on the Borel sets of `ℂ`.** A measure `μ` finite on compact sets is determined by its values on a
countable π-system `C` generating the Borel sets, provided `C` contains an exhausting sequence of sets of compact
closure. -/
theorem measure_ext_of_complex_pi {μ ν : Measure ℂ} [IsFiniteMeasureOnCompacts μ] (C : Set (Set ℂ))
    (hpi : IsPiSystem C) (hgen : MeasurableSpace.generateFrom C = borel ℂ) (B : ℕ → Set ℂ) (hB : ∀ n, B n ∈ C)
    (hcov : ⋃ n, B n = univ) (hcpt : ∀ n, IsCompact (closure (B n))) (h : ∀ S ∈ C, μ S = ν S) : μ = ν := by
  refine Measure.ext_of_generateFrom_of_iUnion C B ?_ hpi hcov hB ?_ h
  · exact BorelSpace.measurable_eq.symm.trans hgen.symm
  · intro n
    exact ne_of_lt ((measure_mono subset_closure).trans_lt (hcpt n).measure_lt_top)

end HarmonicBalls
