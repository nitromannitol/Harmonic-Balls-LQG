import HarmonicBalls.Proofs.Sec8.BallMassSizeScaling

/-! # Translation of annular ball-mass sizes -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Translating a measure by `-z` transports the annular ball-mass size at
`z` to the corresponding centred size. -/
theorem annulusBallMassSize_map_sub (μ : Measure ℂ) (β ρ : ℝ) (z : ℂ) :
    annulusBallMassSize (μ.map (fun x : ℂ => x - z)) β ρ 0 =
      annulusBallMassSize μ β ρ z := by
  have hball (x : ℂ) (r : ℝ) :
      (μ.map (fun w : ℂ => w - z)) (ball x r) = μ (ball (x + z) r) := by
    rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet]
    congr 1
    ext w
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    abel
  have hann (x : ℂ) : x ∈ annulus (0 : ℂ) (ρ / 2) ρ ↔
      x + z ∈ annulus z (ρ / 2) ρ := by
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      sub_zero, add_sub_cancel_right]
  unfold annulusBallMassSize
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun r => le_iInf fun hr => ?_
    have hx' : x - z ∈ annulus (0 : ℂ) (ρ / 2) ρ := by
      apply (hann (x - z)).2
      simpa using hx
    calc
      _ ≤ (μ.map (fun w : ℂ => w - z)) (ball (x - z) r) /
          ENNReal.ofReal ((r / ρ) ^ β) :=
        iInf_le_of_le (x - z) (iInf_le_of_le hx' (iInf_le_of_le r (iInf_le_of_le hr le_rfl)))
      _ = _ := by rw [hball]; simp
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun r => le_iInf fun hr => ?_
    calc
      _ ≤ μ (ball (x + z) r) / ENNReal.ofReal ((r / ρ) ^ β) :=
        iInf_le_of_le (x + z) (iInf_le_of_le ((hann x).1 hx)
          (iInf_le_of_le r (iInf_le_of_le hr le_rfl)))
      _ = _ := by rw [hball]

end HarmonicBalls.Section6
