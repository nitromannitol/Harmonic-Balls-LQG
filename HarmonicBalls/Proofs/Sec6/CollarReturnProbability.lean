import HarmonicBalls.Proofs.Sec6.CollarReturnExhaustion
import MarkovProcess.Path.RelativeHitting
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Probability of returning to an interior core -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- Return to a closed core after exit from an open domain and before exit
from another open domain is a Borel event. -/
theorem measurableSet_core_return {A B C : Set ℂ}
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsClosed C) :
    MeasurableSet {ω : ContinuousPath ℂ | ∃ t : ℝ≥0,
      ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  let q : ℕ → ℝ≥0 := fun k => DenseTime.castOrderEmbedding (DenseTime.enumeration k)
  have heq : {ω : ContinuousPath ℂ | ∃ t : ℝ≥0,
      ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} =
      ⋃ k, ContinuousPath.hitsSetBetween (ContinuousPath.exitTime B) (q k) C ∩
        {ω | (q k : ℝ≥0∞) < ContinuousPath.exitTime A ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, ContinuousPath.hitsSetBetween]
    constructor
    · rintro ⟨t, htB, htA, htC⟩
      obtain ⟨a, hta, haA⟩ := exists_between htA
      have ha0 : a ≠ ∞ := ne_top_of_lt haA
      have hta' : t < a.toNNReal := by
        apply ENNReal.coe_lt_coe.mp
        simpa [ENNReal.coe_toNNReal ha0] using hta
      obtain ⟨v, htv, hva⟩ := DenseTime.exists_cast_btwn hta'
      let k := DenseTime.enumeration.symm v
      have hk : q k = DenseTime.castOrderEmbedding v := by simp [q, k]
      refine ⟨k, ⟨t, htB, ?_, htC⟩, ?_⟩
      · rw [hk]; exact htv.le
      · rw [hk]
        apply lt_trans (ENNReal.coe_lt_coe.mpr hva)
        simpa [ENNReal.coe_toNNReal ha0] using haA
    · rintro ⟨k, ⟨t, htB, htq, htC⟩, hqA⟩
      exact ⟨t, htB, (ENNReal.coe_le_coe.mpr htq).trans_lt hqA, htC⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  exact ((ContinuousPath.canonicalFiltration (alpha := ℂ)).le (q k) _
    (ContinuousPath.measurableSet_hitsSetBetween (ContinuousPath.exitTime B)
      (ContinuousPath.isStoppingTime_exitTime B hB) (q k) C hC)).inter
    (ContinuousPath.measurableSet_lt_exitTime A hA (q k))

/-- The probability of a return to a fixed interior closed core after exiting
an open exhaustion member tends to zero for each Brownian starting point. -/
theorem tendsto_core_return_probability_of_open_exhaustion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C})
      atTop (𝓝 0) := by
  let E : ℕ → Set (ContinuousPath ℂ) := fun n => {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C}
  have hmeas : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_core_return (isOpen_iUnion hopen) (hopen n) hC
  have hae : ∀ᵐ ω ∂planarBrownianMotion x, ∀ᶠ n in atTop, ω ∉ E n := by
    filter_upwards [ae_eventually_no_core_return_of_open_exhaustion hopen hmono hbounded hC hCA hx]
      with ω hω
    filter_upwards [hω] with n hn
    exact hn (D n) Subset.rfl
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := planarBrownianMotion x) (As := E) (A := ∅) atTop MeasurableSet.empty hmeas
    (by filter_upwards [hae] with ω hω; filter_upwards [hω] with n hn; simpa using hn)
  simpa [E] using hlim


/-- The same decay holds for arbitrary domains containing the exhaustion
members, without measurability assumptions on those domains. -/
theorem tendsto_core_return_probability_of_superset_exhaustion
    {D B : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hDB : ∀ n, D n ⊆ B n) (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (B n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_core_return_probability_of_open_exhaustion hopen hmono hbounded hC hCA hx)
  · intro n; exact bot_le
  · intro n
    apply measure_mono
    rintro ω ⟨t, htB, htA, htC⟩
    exact ⟨t, (ContinuousPath.exitTime_mono (hDB n) ω).trans htB, htA, htC⟩


/-- A single exhaustion index controls the return probability uniformly over
all containing domains, for a fixed Brownian starting point. -/
theorem eventually_core_return_probability_lt_of_open_exhaustion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ B : Set ℂ, D n ⊆ B →
      planarBrownianMotion x {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C} < ε := by
  have hlim := tendsto_core_return_probability_of_open_exhaustion hopen hmono hbounded hC hCA hx
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn B hDB
  apply lt_of_le_of_lt (measure_mono ?_) hn
  rintro ω ⟨t, htB, htA, htC⟩
  exact ⟨t, (ContinuousPath.exitTime_mono hDB ω).trans htB, htA, htC⟩

end HarmonicBalls.Section6
