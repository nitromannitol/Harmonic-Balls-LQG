import HarmonicBalls.Steps.SecA.Basic

/-!
# Lemma A.4 (lemma:appendix-zero-boundary, line 3772): carving of the proof

`ObstacleOdometerZeroBoundaryStmt` (Draft/SectionA.lean): for `t > 0` the odometer `v_t = ṽ_t - β_t` vanishes on
`∂B_1`. The printed proof is one line (3777): "immediate from `q_{B_1} ∈ S̃(t)` and `q_{B_1} = G_{B_1}(0,·) = 0` on
`∂B_1`". On `∂B_R`, `β_t = 0 ≤ ṽ_t ≤ q_{B_R} = 0`. Stated for a general radius `R > 0` and pole `z ∈ B_R`:
`ObstacleOdometerZeroBoundaryGeneral`.

## Steps

No step of its own: the reduction `obstacleOdometerZeroBoundaryGeneral_of_steps` is the printed argument, proved,
from the shared steps (Basic.lean) `GreenPotentialBallContinuousStep` and `GreenPotentialBallLaplacianStep`, which
give `q_{B_R} ∈ S̃(t)`. The zero boundary values of `q_{B_R}` and `G_{B_R}(z,·)` hold by definition
(`greenPotentialBall_eq_zero_of_notMem`, `obstacle_eq_zero_of_notMem`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Lemma A.4 for a general radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`). -/
def ObstacleOdometerZeroBoundaryGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t → ∀ x ∈ sphere (0 : ℂ) R, shiftedOdometer μ R z t x = 0

/-- **Lemma A.4, general radius and pole, from the shared steps** (the argument of line 3777). -/
theorem obstacleOdometerZeroBoundaryGeneral_of_steps (hq : GreenPotentialBallContinuousStep)
    (hΔq : GreenPotentialBallLaplacianStep) : ObstacleOdometerZeroBoundaryGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht x hx
  have hxb : x ∉ ball (0 : ℂ) R := fun h => (mem_ball.1 h).ne (mem_sphere.1 hx)
  have hxc : x ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hx
  have hxz : x ≠ z := fun h => hxb (h ▸ hz)
  have hqS : greenPotentialBall μ R ∈ shiftedSupersolutions μ R z t :=
    greenPotentialBall_mem_shiftedSupersolutions ht.le (hq μ hμ R βm βp hR hV)
      (hΔq μ hμ R βm βp hR hV).laplacianLE
  have hle := shiftedLeastSupersolution_le hqS hxc hxz
  have hge := obstacle_le_shiftedLeastSupersolution ⟨_, hqS⟩ hxc hxz
  rw [obstacle_eq_zero_of_notMem hxb] at hge
  rw [greenPotentialBall_eq_zero_of_notMem hxb] at hle
  simp only [shiftedOdometer, obstacle_eq_zero_of_notMem hxb, sub_zero]
  exact le_antisymm hle hge

/-- The general form of Lemma A.4 gives the printed statement (`R = 1`, `z = 0`). -/
theorem obstacleOdometerZeroBoundary_of_general (h : ObstacleOdometerZeroBoundaryGeneral) :
    ObstacleOdometerZeroBoundaryStmt := fun μ hμ βm βp hV t ht x hx =>
  h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t ht x hx

/-- **Lemma A.4 from the shared steps.** -/
theorem obstacleOdometerZeroBoundary_of_steps (hq : GreenPotentialBallContinuousStep)
    (hΔq : GreenPotentialBallLaplacianStep) : ObstacleOdometerZeroBoundaryStmt :=
  obstacleOdometerZeroBoundary_of_general (obstacleOdometerZeroBoundaryGeneral_of_steps hq hΔq)

end HarmonicBalls
