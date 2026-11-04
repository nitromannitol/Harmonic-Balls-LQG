import HarmonicBalls.Proofs.Sec8.GoodEventMeasurable

/-! # Good-annulus measurability for extreme parameters -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- If the mass threshold is at least the whole annulus and `b < 1`, the
annulus itself witnesses failure of the good-annulus condition. -/
theorem not_isGoodAnnulus_of_one_le_mass_of_lt_one_probability
    (μ : Measure ℂ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) {a b : ℝ}
    (ha : 1 ≤ a) (hb : b < 1) : ¬ IsGoodAnnulus μ r z a b := by
  intro hgood
  let A : Set ℂ := annulus z (3 * r) (5 * r)
  have hmass : μ A ≤ ENNReal.ofReal a * μ A := by
    calc
      μ A = 1 * μ A := (one_mul _).symm
      _ ≤ ENNReal.ofReal a * μ A := mul_le_mul' (ENNReal.one_le_ofReal.mpr ha) le_rfl
  have hu : z + (((4 * r : ℝ) : ℂ)) ∈ sphere z (4 * r) := by
    simp [hr]
  have h := hgood A (isOpen_ball.sdiff isClosed_closedBall).measurableSet Subset.rfl hmass _ hu
  have hp : planarBrownianMotion (z + (((4 * r : ℝ) : ℂ)))
      {p | ContinuousPath.exitTime A p ≤ ContinuousPath.exitTime A p} = 1 := by simp
  rw [hp] at h
  exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr hb)) h

/-- For mass threshold at least one, the unit good-annulus event is measurable
for every probability threshold, with no conditions on the measure. -/
theorem measurableSet_unit_isGoodAnnulus_of_one_le_mass {a : ℝ} (ha : 1 ≤ a) (b : ℝ) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} := by
  by_cases hb : 1 ≤ b
  · have heq : {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} = univ := by
      ext μ
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact isGoodAnnulus_of_one_le μ 1 0 a hb
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} = ∅ := by
      ext μ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_isGoodAnnulus_of_one_le_mass_of_lt_one_probability μ (by norm_num) 0 ha (lt_of_not_ge hb)
    rw [heq]
    exact MeasurableSet.empty

end HarmonicBalls
