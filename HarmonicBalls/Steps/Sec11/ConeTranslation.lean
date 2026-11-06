import HarmonicBalls.Steps.Sec11.ConeDilation
import HarmonicBalls.Proofs.Sec6.GreenSizeTranslation

/-! # Translation covariance of cone mass events -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Translating the measure back to the origin transports the cone event,
including the annular Green-potential supremum. -/
theorem coneMassEvent_map_sub_iff (μ : Measure ℂ) (Q : Set ℂ) (hQ : IsCone Q)
    (M r : ℝ) (z : ℂ) :
    coneMassEvent (μ.map (fun y : ℂ => y - z)) Q M r 0 ↔
      coneMassEvent μ Q M r z := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hcone : coneAt Q 0 = Q := by simp [coneAt]
  have hset : MeasurableSet (annulus (0 : ℂ) r (2 * r) ∩ coneAt Q 0) := by
    rw [hcone]
    exact (measurableSet_ball.diff measurableSet_closedBall).inter hQm
  have hpre : (fun y : ℂ => y - z) ⁻¹' (annulus (0 : ℂ) r (2 * r) ∩ coneAt Q 0) =
      annulus z r (2 * r) ∩ coneAt Q z := by
    ext y
    simp only [mem_preimage, mem_inter_iff, hcone]
    have ha : y - z ∈ annulus (0 : ℂ) r (2 * r) ↔ y ∈ annulus z r (2 * r) := by
      simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
    have hb : y - z ∈ Q ↔ y ∈ coneAt Q z := by
      constructor
      · intro hy
        exact ⟨y - z, hy, sub_add_cancel y z⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    exact and_congr ha hb
  unfold coneMassEvent
  rw [Measure.map_apply (by fun_prop) hset, hpre, Section6.annulusGreenPotentialSup_map_sub]

end HarmonicBalls

#print axioms HarmonicBalls.coneMassEvent_map_sub_iff
