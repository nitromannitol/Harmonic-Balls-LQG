import HarmonicBalls.Proofs.Sec6.FineSupportCompactReduction
import MarkovProcess.Path.ExitTime
import Mathlib.Probability.Independence.ZeroOne

/-! # Germ measurability of instant hitting

The event that a countable union of compact sets is hit at time zero belongs
to every positive-time Brownian path sigma-algebra.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal Topology

/-- Instantaneous hitting of a countable union of compact sets is measurable
at every positive time in the canonical filtration. -/
theorem measurableSet_instant_hit_compact_union_canonical
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (t : NNReal) (ht : 0 < t) :
    MeasurableSet[ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω : ContinuousPath ℂ | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} := by
  let q : ℕ → NNReal := fun n => min t ((1 / 2 : NNReal) ^ n)
  have hqpos (n : ℕ) : 0 < q n := lt_min ht (pow_pos (by norm_num) _)
  have hqle (n : ℕ) : q n ≤ t := min_le_left _ _
  have hq : Tendsto (fun n => (q n : ℝ≥0∞)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => ((1 / 2 : NNReal) ^ n)) atTop (𝓝 0) :=
      NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hm : Tendsto q atTop (𝓝 0) := by
      simpa [q] using (tendsto_const_nhds.min hp)
    have hf := ENNReal.continuous_coe.continuousAt.tendsto.comp hm
    change Tendsto (fun n => (q n : ℝ≥0∞)) atTop (𝓝 ((0 : NNReal) : ℝ≥0∞)) at hf
    simpa using hf
  have heq : {ω : ContinuousPath ℂ | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} =
      ⋂ m, ⋃ n, {ω | ContinuousPath.exitTime (K n)ᶜ ω ≤ (q m : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hz m
      have hlt : (⨅ n, ContinuousPath.exitTime (K n)ᶜ ω) < (q m : ℝ≥0∞) := by
        rw [← exitTime_compl_iUnion, hz]
        exact ENNReal.coe_pos.mpr (hqpos m)
      obtain ⟨n, hn⟩ := iInf_lt_iff.mp hlt
      exact ⟨n, hn.le⟩
    · intro hall
      apply le_antisymm _ bot_le
      apply ge_of_tendsto hq
      filter_upwards [] with m
      obtain ⟨n, hn⟩ := hall m
      rw [exitTime_compl_iUnion]
      exact (iInf_le (fun n => ContinuousPath.exitTime (K n)ᶜ ω) n).trans hn
  rw [heq]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro n
  have hmeas := ContinuousPath.measurableSet_hitsSetBy (q m) (K n) (hK n).isClosed
  have hevent : {ω : ContinuousPath ℂ | ContinuousPath.exitTime (K n)ᶜ ω ≤
      (q m : ℝ≥0∞)} = ContinuousPath.hitsSetBy (q m) (K n) := by
    ext ω
    simpa using ContinuousPath.exitTime_le_iff_mem_hitsSetBy (K n)ᶜ
      (hK n).isClosed.isOpen_compl (q m) ω
  rw [hevent]
  exact (ContinuousPath.canonicalFiltration (alpha := ℂ)).mono (hqle m) _ hmeas

/-- Instantaneous hitting of a countable compact union belongs to the germ
sigma-algebra of the canonical filtration. -/
theorem measurableSet_instant_hit_compact_union_germ
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) :
    MeasurableSet[⨅ (t : NNReal) (_ : 0 < t),
      ContinuousPath.canonicalFiltration (alpha := ℂ) t]
      {ω : ContinuousPath ℂ | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} := by
  rw [MeasurableSpace.measurableSet_iInf]
  intro t
  rw [MeasurableSpace.measurableSet_iInf]
  intro ht
  exact measurableSet_instant_hit_compact_union_canonical K hK t ht

/-- Self-independence of the Brownian germ yields the zero-one step for
instantaneous hitting of a countable union of compact sets. -/
theorem ae_instant_hit_of_germ_indep (x : ℂ)
    (hindep : ProbabilityTheory.Indep
      (⨅ (t : NNReal) (_ : 0 < t), ContinuousPath.canonicalFiltration (alpha := ℂ) t)
      (⨅ (t : NNReal) (_ : 0 < t), ContinuousPath.canonicalFiltration (alpha := ℂ) t)
      (planarBrownianMotion x))
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hpos : 0 < planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0}) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0 := by
  have h01 := ProbabilityTheory.measure_eq_zero_or_one_of_indep_self hindep
    (measurableSet_instant_hit_compact_union_germ K hK)
  have hone : planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} = 1 := by
    rcases h01 with hz | ho
    · exact (ne_of_gt hpos hz).elim
    · exact ho
  apply (MeasureTheory.mem_ae_iff_prob_eq_one ?_).mpr hone
  exact measurableSet_eq_fun (measurable_exitTime_compl_iUnion_compact K hK) measurable_const

end HarmonicBalls.Section6
