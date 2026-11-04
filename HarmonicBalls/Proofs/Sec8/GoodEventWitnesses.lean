import HarmonicBalls.Proofs.Sec8.GoodEventMeasurable

/-! # Countable witnesses for a bad annulus

For a fixed Borel test set, the Brownian survival probability does not depend
on the measure. Consequently, the measures for which that set witnesses a
bad annulus form a measurable set. A countable family of witnesses would
therefore settle good-annulus event measurability. The existence of such a
family is left as an explicit mathematical condition.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- Measures for which a fixed set and a starting point witness failure of
the good-annulus condition. -/
def goodAnnulusBadWitness (r : ℝ) (z : ℂ) (a b : ℝ) (Y : Set ℂ) : Set (Measure ℂ) :=
  {μ | MeasurableSet Y ∧ Y ⊆ annulus z (3 * r) (5 * r) ∧
    μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ∧
    ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b <
      planarBrownianMotion u
        {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime Y p}}

/-- A fixed Borel test set gives a measurable set of bad measures. The
Brownian probability is a constant as the measure varies. -/
theorem measurableSet_goodAnnulusBadWitness (r : ℝ) (z : ℂ) (a b : ℝ) (Y : Set ℂ) :
    MeasurableSet (goodAnnulusBadWitness r z a b Y) := by
  classical
  by_cases hY : MeasurableSet Y
  · have hmass : MeasurableSet {μ : Measure ℂ |
        μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))} :=
      measurableSet_le (Measure.measurable_coe hY)
        (measurable_const.mul (Measure.measurable_coe
          (isOpen_ball.sdiff isClosed_closedBall).measurableSet))
    by_cases hfixed : Y ⊆ annulus z (3 * r) (5 * r) ∧
      ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b <
        planarBrownianMotion u
          {p | MarkovProcess.ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            MarkovProcess.ContinuousPath.exitTime Y p}
    · convert hmass using 1
      ext μ
      change (MeasurableSet Y ∧ Y ⊆ annulus z (3 * r) (5 * r) ∧
        μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ∧ _) ↔ _
      exact ⟨fun h => h.2.2.1, fun h => ⟨hY, hfixed.1, h, hfixed.2⟩⟩
    · have hempty : goodAnnulusBadWitness r z a b Y = ∅ := by
        ext μ
        simp only [goodAnnulusBadWitness, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨_, hy, _, hp⟩
        exact hfixed ⟨hy, hp⟩
      rw [hempty]
      exact MeasurableSet.empty
  · have hempty : goodAnnulusBadWitness r z a b Y = ∅ := by
      ext μ
      simp [goodAnnulusBadWitness, hY]
    rw [hempty]
    exact MeasurableSet.empty

/-- Failure of the good-annulus condition is exactly the existence of a
Borel witness with Brownian survival probability exceeding the threshold. -/
theorem not_isGoodAnnulus_iff_exists_badWitness (μ : Measure ℂ)
    (r : ℝ) (z : ℂ) (a b : ℝ) :
    ¬ IsGoodAnnulus μ r z a b ↔ ∃ Y, μ ∈ goodAnnulusBadWitness r z a b Y := by
  classical
  simp only [IsGoodAnnulus, goodAnnulusBadWitness, mem_ofPred_eq]
  push Not
  rfl

/-- A countable family that captures every bad measure gives a measurable
full good-annulus event. The witness-capture hypothesis is not asserted here. -/
theorem measurableSet_isGoodAnnulus_of_countable_witnesses
    (r : ℝ) (z : ℂ) (a b : ℝ) (Y : ℕ → Set ℂ)
    (hwitness : ∀ μ : Measure ℂ, ¬ IsGoodAnnulus μ r z a b →
      ∃ n, μ ∈ goodAnnulusBadWitness r z a b (Y n)) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} := by
  have heq : {μ : Measure ℂ | ¬ IsGoodAnnulus μ r z a b} =
      ⋃ n, goodAnnulusBadWitness r z a b (Y n) := by
    ext μ
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · exact hwitness μ
    · intro ⟨n, hn⟩
      exact (not_isGoodAnnulus_iff_exists_badWitness μ r z a b).2 ⟨Y n, hn⟩
  have hbad : MeasurableSet {μ : Measure ℂ | ¬ IsGoodAnnulus μ r z a b} := by
    rw [heq]
    exact MeasurableSet.iUnion fun n => measurableSet_goodAnnulusBadWitness r z a b (Y n)
  simpa only [compl_ofPred, not_not] using hbad.compl

end HarmonicBalls
