import HarmonicBalls.Steps.Sec9.ObstacleComparison
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# Lemma 9.1: proof of the steps

Proofs of the steps of `HarmonicBalls/Steps/Sec9/ObstacleComparison.lean` and of `ObstacleComparisonStmt`
(Lemma 9.1, lemma:obstacle-comp, line 2279 of paper/lqg_harmonic_ball-corrected.tex). No literature input is used:
the symmetry of the Green function of a disc is `greenFunction_ball_comm` (explicit formula,
HarmonicBalls/Proofs/Potential/GreenBall.lean).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

theorem greenFunctionBallSymmetric : GreenFunctionBallSymmetric :=
  greenFunction_ball_comm

/-- `-G_O(·,x)`, `x ∈ O \ {z}`, is the test function of eq:sub-harmonic-potential with `ν₁ = 0`, `ν₂ = δ_x`
(compact support `{x} ⊆ O`) and `q = 0`; it is finite at the centre (`δ_x({z}) = 0`). -/
theorem negGreenFunctionMemSubharmonicBallTestClass : NegGreenFunctionMemSubharmonicBallTestClass := by
  intro O Λ z x hO hcl hx hxz
  refine ⟨O, {x}, 0, Measure.dirac x, 0, hO, hcl, isCompact_singleton, singleton_subset_iff.2 hx,
    inferInstance, inferInstance, by simp, by simp, by simp, harmonicOnNhd_const 0, ?_,
    integrable_dirac enorm_lt_top, ?_⟩
  · simp [Measure.dirac_apply' _ (measurableSet_singleton z), hxz]
  · funext w
    simp [greenPotential, integral_dirac]

/-- Lemma 9.1 (lemma:obstacle-comp, line 2279). -/
theorem obstacleComparison : ObstacleComparisonStmt :=
  obstacleComparison_of_steps greenFunctionBallSymmetric negGreenFunctionMemSubharmonicBallTestClass

end HarmonicBalls
