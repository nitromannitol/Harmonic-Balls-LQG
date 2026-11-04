import HarmonicBalls.Proofs.Sec8.ExceptionalStartingAtoms

/-! # Reduction to concentrated bad witnesses

Strict compact-obstacle tests leave only witnesses whose threshold mass is
concentrated at their starting point.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- Once strict compact-obstacle tests are imposed, it suffices to test sets
whose entire mass is a threshold-sized atom at the starting point. -/
theorem isGoodAnnulus_iff_compact_and_concentrated_tests
    (μ : Measure ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      (∀ K : Set ℂ, IsCompact K → K ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ K) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ K) p} ≤ ENNReal.ofReal b) ∧
      (∀ Y : Set ℂ, MeasurableSet Y → Y ⊆ annulus z (3 * r) (5 * r) →
        μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), u ∈ Y →
          μ {u} = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
          μ (Y \ {u}) = 0 →
          planarBrownianMotion u
            {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
              ContinuousPath.exitTime Y p} ≤ ENNReal.ofReal b) := by
  have hA : IsOpen (annulus z (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  constructor
  · intro hgood
    constructor
    · intro K hK hKA hmass u hu
      exact hgood _ (hA.measurableSet.diff hK.measurableSet) sdiff_subset hmass.le u hu
    · intro Y hY hYA hmass u hu _ _ _
      exact hgood Y hY hYA hmass u hu
  · rintro ⟨hcomp, hconc⟩
    by_contra hbad
    obtain ⟨Y, hY, hYA, u, hu, huY, hatom, hzero, hp⟩ :=
      exists_threshold_atom_badWitness_of_compact_tests μ r hr z a b hfinite hsmall hcomp hbad
    have hmass : μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := by
      have hsub : Y ⊆ (Y \ {u}) ∪ {u} := by
        intro x hx
        by_cases hxu : x = u
        · exact Or.inr (by simpa using hxu)
        · exact Or.inl ⟨hx, by simpa using hxu⟩
      calc
        μ Y ≤ μ (Y \ {u}) + μ {u} := (measure_mono hsub).trans (measure_union_le _ _)
        _ = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := by rw [hzero, zero_add, hatom]
    exact (not_le_of_gt hp) (hconc Y hY hYA hmass u hu huY hatom hzero)

end HarmonicBalls
