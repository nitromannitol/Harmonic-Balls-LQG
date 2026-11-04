import HarmonicBalls.Proofs.Sec8.AtomicWitnessRemoval
import HarmonicBalls.Proofs.Sec8.CountableCompactObstacles

/-! # Countable obstacles for measures with atoms

The rational compact-obstacle family represents the good-annulus test when
all atoms on the starting sphere have mass strictly below the threshold.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

open MarkovProcess in
/-- Under the interior small-ball hitting estimate, a finite measure whose starting
atoms are below the threshold passes the good-annulus test exactly when it passes all rational obstacle
tests. The family is countable whenever `D` is countable. -/
theorem isGoodAnnulus_iff_rationalBallObstacles_of_small_starting_atoms
    {D : Set ℂ} (hD : Dense D) (μ : Measure ℂ)
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hatoms : ∀ u ∈ sphere z (4 * r), μ {u} <
      ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      ∀ s : Finset (D × ℚ), rationalBallObstacle D s ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ rationalBallObstacle D s) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} ≤ ENNReal.ofReal b := by
  let U := annulus z (3 * r) (5 * r)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hbounded : Bornology.IsBounded U := isBounded_ball.subset sdiff_subset
  have hcenter : ∀ u ∈ sphere z (4 * r), u ∈ U := by
    intro u hu
    simp only [mem_sphere] at hu
    change u ∈ ball z (5 * r) \ closedBall z (3 * r)
    simp only [mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith
  constructor
  · intro hgood s hs hmass u hu
    have h := hgood (U \ rationalBallObstacle D s)
      (hU.measurableSet.diff (isCompact_rationalBallObstacle D s).measurableSet)
      sdiff_subset hmass.le u hu
    have heq : {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (U \ rationalBallObstacle D s) p} =
        {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} := by
      ext p
      exact stay_sdiff_iff_avoid U (rationalBallObstacle D s) p
    rw [← heq]
    exact h
  · intro htest
    apply (isGoodAnnulus_iff_compact_obstacles_of_small_starting_atoms
      μ r z a b hfinite hatoms hsmall).2
    intro K hK hKU hmass u hu
    by_contra hnot
    have hp : ENNReal.ofReal b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p} := by
      have := lt_of_not_ge hnot
      convert this using 1
      congr 1
      ext p
      exact (stay_sdiff_iff_avoid U K p).symm
    obtain ⟨s, hKs, hsU, hprob⟩ := exists_rationalBallObstacle_of_avoid_gt
      hD hU hbounded hK hKU (hcenter u hu) (ENNReal.ofReal b) hp
    have hmass' : μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U :=
      (measure_mono (show U \ rationalBallObstacle D s ⊆ U \ K from
        fun x hx => ⟨hx.1, fun hxK => hx.2 (hKs hxK)⟩)).trans_lt hmass
    exact (not_le_of_gt hprob) (htest s hsU hmass' u hu)

open MarkovProcess in
/-- A single Borel set of measures represents the good-annulus event on
finite measures with starting atoms below the mass threshold, conditional on the
interior small-ball hitting estimate. -/
theorem exists_measurable_isGoodAnnulus_of_small_starting_atoms
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧
      ∀ (μ : Measure ℂ),
        μ (annulus z (3 * r) (5 * r)) ≠ ∞ →
        (∀ u ∈ sphere z (4 * r), μ {u} <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) →
        (μ ∈ G ↔ IsGoodAnnulus μ r z a b) := by
  classical
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable D := hDc.to_subtype
  let U := annulus z (3 * r) (5 * r)
  let Bad (s : Finset (D × ℚ)) : Set (Measure ℂ) :=
    {μ | rationalBallObstacle D s ⊆ U ∧
      μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U ∧
      ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p}}
  have hBad (s : Finset (D × ℚ)) : MeasurableSet (Bad s) := by
    have hmass : MeasurableSet {μ : Measure ℂ |
        μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U} :=
      measurableSet_lt (Measure.measurable_coe
        ((isOpen_ball.sdiff isClosed_closedBall).measurableSet.diff
          (isCompact_rationalBallObstacle D s).measurableSet))
        (measurable_const.mul (Measure.measurable_coe
          (isOpen_ball.sdiff isClosed_closedBall).measurableSet))
    by_cases hcond : rationalBallObstacle D s ⊆ U ∧
        ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
          {p | ContinuousPath.exitTime U p ≤
            ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p}
    · have heq : Bad s = {μ : Measure ℂ |
          μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U} := by
        ext μ
        simp only [Bad, mem_ofPred_eq]
        exact ⟨fun h => h.2.1, fun h => ⟨hcond.1, h, hcond.2⟩⟩
      rw [heq]
      exact hmass
    · have heq : Bad s = ∅ := by
        ext μ
        simp only [Bad, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hs, _, hp⟩
        exact hcond ⟨hs, hp⟩
      rw [heq]
      exact MeasurableSet.empty
  refine ⟨(⋃ s, Bad s)ᶜ, (MeasurableSet.iUnion hBad).compl, ?_⟩
  intro μ hfinite hatoms
  rw [isGoodAnnulus_iff_rationalBallObstacles_of_small_starting_atoms
    hD μ r hr z a b hfinite hatoms hsmall]
  simp only [mem_compl_iff, mem_iUnion, Bad, mem_ofPred_eq, not_exists, not_and]
  constructor
  · intro h s hs hm u hu
    exact le_of_not_gt (h s hs hm u hu)
  · intro h s hs hm u hu
    exact not_lt_of_ge (h s hs hm u hu)

end HarmonicBalls
