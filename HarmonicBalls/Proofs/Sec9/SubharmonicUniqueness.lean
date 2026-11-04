import HarmonicBalls.Proofs.Sec9.ObstacleComparison
import HarmonicBalls.Steps.Sec9.SubharmonicUniqueness

/-!
# Green test functions for Proposition 9.2

The positive Green function with pole outside a subharmonic ball is admissible as a test
function, as is its negative. The resulting inequalities give the required equality off the ball.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

/-- The Green function with pole outside the ball is a subharmonic-ball test function. -/
theorem greenFunction_mem_subharmonicBallTestClass {O A : Set ℂ} {z x : ℂ}
    (hO : IsOpen O) (hA : IsOpen A) (hcl : closure A ⊆ O) (hx : x ∈ O \ A) :
    (fun w => greenFunction O w x) ∈ subharmonicBallTestClass A z := by
  refine ⟨O, {x}, Measure.dirac x, 0, 0, hO, hcl, isCompact_singleton, singleton_subset_iff.2 hx.1,
    inferInstance, inferInstance, by simp, by simp, ?_, harmonicOnNhd_const 0, by simp, by simp, ?_⟩
  · simp [Measure.dirac_apply' _ hA.measurableSet, hx.2]
  · funext w
    simp [greenPotential, integral_dirac]

/-- The Green potential comparison vanishes outside a subharmonic ball. -/
theorem IsSubharmonicBall.greenPotential_eq {μ : Measure ℂ} {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R : ℝ} (hcl : closure A ⊆ ball 0 R) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R \ A) :
    μ.real A * greenFunction (ball 0 R) x z - ∫ y in A, greenFunction (ball 0 R) x y ∂μ = 0 := by
  have hxz : x ≠ z := fun h => hx.2 (h ▸ hA.2.1)
  have hle := hA.greenPotential_le_of_steps greenFunctionBallSymmetric
    negGreenFunctionMemSubharmonicBallTestClass hcl hx.1 hxz
  have hge := (hA.2.2.2.2 _ (greenFunction_mem_subharmonicBallTestClass isOpen_ball hA.1 hcl hx)).2
  have hint : ∫ w in A, greenFunction (ball 0 R) w x ∂μ = ∫ y in A, greenFunction (ball 0 R) x y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun w => greenFunction_ball_comm R w x)
  beta_reduce at hge
  rw [hint, greenFunction_ball_comm R z x] at hge
  linarith

/-- The cluster is contained in a subharmonic ball once the negative Green potential of the
ball has been shown to be an admissible supersolution. -/
theorem IsSubharmonicBall.cluster_subset_of_neg_greenPotential_mem_supersolutions
    {μ : Measure ℂ} {A : Set ℂ} {z : ℂ} (hA : IsSubharmonicBall μ A z) {R t : ℝ}
    (hcl : closure A ⊆ ball 0 R) (hmass : μ.real A = t)
    (hw : (fun x => -∫ y in A, greenFunction (ball 0 R) y x ∂μ) ∈ supersolutions μ R z t) :
    cluster μ R z t ⊆ A := by
  apply cluster_subset_of_supersolution hA.2.1 hw
  intro x hx
  have heq := hA.greenPotential_eq hcl hx
  have hint : ∫ y in A, greenFunction (ball 0 R) y x ∂μ = ∫ y in A, greenFunction (ball 0 R) x y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R y x)
  rw [hint, greenFunction_ball_comm R z x]
  rw [hmass] at heq
  linarith

end HarmonicBalls
