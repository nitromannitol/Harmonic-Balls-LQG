import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation
import HarmonicBalls.Steps.Sec11.ConeGeometry
import HarmonicBalls.Proofs.GFF.FixedShiftCircleLQGRepresentation

/-! # Dilation covariance of cone mass events -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set
open scoped ENNReal

/-- A positive spatial dilation transports the cone event at the origin. -/
theorem coneMassEvent_map_inv_smul_iff (μ : Measure ℂ) (Q : Set ℂ) (hQ : IsCone Q)
    (M r : ℝ) {k : ℝ} (hk : 0 < k) :
    coneMassEvent (μ.map (fun y : ℂ => k⁻¹ • y)) Q M r 0 ↔
      coneMassEvent μ Q M (k * r) 0 := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hcone : coneAt Q 0 = Q := by simp [coneAt]
  have hpre : (fun y : ℂ => k⁻¹ • y) ⁻¹' Q = Q := by
    ext x
    exact hQ.smul_mem_iff x (inv_pos.mpr hk)
  have hset : MeasurableSet (annulus (0 : ℂ) r (2 * r) ∩ coneAt Q 0) := by
    rw [hcone]
    exact (measurableSet_ball.diff measurableSet_closedBall).inter hQm
  have hmass : (μ.map (fun y : ℂ => k⁻¹ • y))
      (annulus 0 r (2 * r) ∩ coneAt Q 0) =
      μ (annulus 0 (k * r) (2 * (k * r)) ∩ coneAt Q 0) := by
    rw [Measure.map_apply (by fun_prop) hset, preimage_inter,
      preimage_inv_smul_annulus hk, hcone, hpre]
    simp only [smul_zero]
    congr 2; ring
  unfold coneMassEvent
  rw [hmass, annulusGreenPotentialSup_comp_real_smul μ hk]
  simp only [smul_zero]
  ring_nf

end HarmonicBalls
