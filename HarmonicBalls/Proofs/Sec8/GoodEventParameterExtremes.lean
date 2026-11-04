import HarmonicBalls.Proofs.Sec8.GoodEventMeasurable

/-! # Good-annulus measurability for extreme parameters -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- If the entire annulus satisfies the mass constraint, it witnesses failure
whenever the probability threshold is less than one. -/
theorem not_isGoodAnnulus_of_annulus_mass_le
    (μ : Measure ℂ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) (a : ℝ) {b : ℝ}
    (hb : b < 1)
    (hmass : μ (annulus z (3 * r) (5 * r)) ≤
      ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) :
    ¬ IsGoodAnnulus μ r z a b := by
  intro hgood
  let A : Set ℂ := annulus z (3 * r) (5 * r)
  have hu : z + (((4 * r : ℝ) : ℂ)) ∈ sphere z (4 * r) := by
    simp [hr]
  have h := hgood A (isOpen_ball.sdiff isClosed_closedBall).measurableSet Subset.rfl hmass _ hu
  have hp : planarBrownianMotion (z + (((4 * r : ℝ) : ℂ)))
      {p | ContinuousPath.exitTime A p ≤ ContinuousPath.exitTime A p} = 1 := by simp
  rw [hp] at h
  exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr hb)) h

/-- In the nontrivial parameter range a good annulus has strictly positive,
finite measure, even for arbitrary measures with atoms. -/
theorem isGoodAnnulus_annulus_mass_ne_zero_ne_top
    (μ : Measure ℂ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hgood : IsGoodAnnulus μ r z a b) :
    μ (annulus z (3 * r) (5 * r)) ≠ 0 ∧
      μ (annulus z (3 * r) (5 * r)) ≠ ∞ := by
  constructor
  · intro hz
    apply not_isGoodAnnulus_of_annulus_mass_le μ hr z a hb _ hgood
    simp [hz]
  · intro ht
    apply not_isGoodAnnulus_of_annulus_mass_le μ hr z a hb _ hgood
    simp [ht, (ENNReal.ofReal_pos.mpr ha).ne']

/-- If the mass threshold is at least the whole annulus and `b < 1`, the
annulus itself witnesses failure of the good-annulus condition. -/
theorem not_isGoodAnnulus_of_one_le_mass_of_lt_one_probability
    (μ : Measure ℂ) {r : ℝ} (hr : 0 ≤ r) (z : ℂ) {a b : ℝ}
    (ha : 1 ≤ a) (hb : b < 1) : ¬ IsGoodAnnulus μ r z a b := by
  apply not_isGoodAnnulus_of_annulus_mass_le μ hr z a hb
  calc
    μ (annulus z (3 * r) (5 * r)) = 1 * μ (annulus z (3 * r) (5 * r)) := (one_mul _).symm
    _ ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) :=
      mul_le_mul' (ENNReal.one_le_ofReal.mpr ha) le_rfl

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

/-- In the nontrivial range, a Borel representative on measures assigning
positive finite mass to the unit annulus suffices for global measurability. -/
theorem measurableSet_unit_isGoodAnnulus_of_positive_finite_mass_version
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (G : Set (Measure ℂ)) (hG : MeasurableSet G)
    (hrep : ∀ μ : Measure ℂ, μ (annulus 0 3 5) ≠ 0 → μ (annulus 0 3 5) ≠ ∞ →
      (μ ∈ G ↔ IsGoodAnnulus μ 1 0 a b)) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} := by
  let A : Set ℂ := annulus 0 3 5
  have hmass : Measurable (fun μ : Measure ℂ => μ A) :=
    Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have heq : {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} =
      G ∩ {μ | μ A ≠ 0} ∩ {μ | μ A ≠ ∞} := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro h
      have hp := isGoodAnnulus_annulus_mass_ne_zero_ne_top μ (by norm_num) 0 ha hb h
      have hp' : μ A ≠ 0 ∧ μ A ≠ ∞ := by simpa [A] using hp
      exact ⟨⟨(hrep μ hp'.1 hp'.2).2 h, hp'.1⟩, hp'.2⟩
    · rintro ⟨⟨hGμ, hzero⟩, htop⟩
      exact (hrep μ hzero htop).1 hGμ
  rw [heq]
  exact (hG.inter (hmass (measurableSet_singleton 0)).compl).inter
    (hmass (measurableSet_singleton ∞)).compl

end HarmonicBalls
