import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Basic.ENNReal.BigOperators

/-! # Selection of a positive-mass tile class -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal BigOperators

/-- If finitely many sets cover `S` and its mass exceeds the sum of identical
    thresholds, at least one of the covering sets exceeds the threshold. -/
theorem exists_cover_member_measure_gt {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (S : Set X) (C : ι → Set X) (c : ℝ≥0∞)
    (hcover : S ⊆ ⋃ i, C i) (hmass : (∑ _i : ι, c) < μ S) :
    ∃ i, c < μ (C i) := by
  classical
  by_contra hn
  have hle : ∀ i, μ (C i) ≤ c := by
    intro i
    exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
  have hsum : μ S ≤ ∑ _i : ι, c := by
    calc
      μ S ≤ μ (⋃ i, C i) := measure_mono hcover
      _ ≤ ∑ i, μ (C i) := measure_iUnion_fintype_le μ C
      _ ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => hle i
  exact (not_lt_of_ge hsum) hmass

/-- On a positive-probability event, one deterministic member of a finite
    cover carries more than its prescribed share of the mass with positive
    probability. No measurability of the events is required. -/
theorem exists_positive_measure_cover_member {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Fintype ι]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S : Set X) (C : ι → Set X) (c : ℝ≥0∞)
    (hcover : S ⊆ ⋃ i, C i)
    (hp : 0 < P {ω | ω ∈ A ∧ (∑ _i : ι, c) < μ ω S}) :
    ∃ i, 0 < P {ω | ω ∈ A ∧ c < μ ω (C i)} := by
  classical
  let E : ι → Set Ω := fun i => {ω | ω ∈ A ∧ c < μ ω (C i)}
  have hsub : {ω | ω ∈ A ∧ (∑ _i : ι, c) < μ ω S} ⊆ ⋃ i, E i := by
    intro ω hω
    obtain ⟨i, hi⟩ := exists_cover_member_measure_gt (μ ω) S C c hcover hω.2
    exact mem_iUnion.mpr ⟨i, hω.1, hi⟩
  have hpos : 0 < P (⋃ i, E i) := hp.trans_le (measure_mono hsub)
  obtain ⟨i, hi⟩ := exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hpos)
  exact ⟨i, hi⟩

/-- The four-class instance used for parity classes of square tiles: if the
    square has mass greater than `8c`, one fixed class has mass greater than
    `2c` on a positive-probability event. -/
theorem exists_positive_measure_four_tile_class {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S : Set X) (C : Fin 4 → Set X) (c : ℝ≥0∞)
    (hcover : S ⊆ ⋃ i, C i)
    (hp : 0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}) :
    ∃ i, 0 < P {ω | ω ∈ A ∧ (2 : ℝ≥0∞) * c < μ ω (C i)} := by
  apply exists_positive_measure_cover_member P μ A S C ((2 : ℝ≥0∞) * c) hcover
  have heq : (∑ _i : Fin 4, (2 : ℝ≥0∞) * c) = (8 : ℝ≥0∞) * c := by
    simp [Finset.sum_const, nsmul_eq_mul]
    rw [← mul_assoc]
    norm_num
  simpa only [heq] using hp

end HarmonicBalls
