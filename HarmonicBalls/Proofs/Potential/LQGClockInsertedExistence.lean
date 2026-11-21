import HarmonicBalls.Proofs.Potential.LQGClockInsertedOfExterior
import HarmonicBalls.Proofs.Potential.LQGClockExteriorClockConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExteriorExhaustion

/-! # Existence of the LQG clock of the inserted field

For `0 < γ` with `γ ^ 2 < 2` and every insertion `α < Q`, the inserted circle-average field of
the whole-plane Gaussian free field has, from every start, an LQG clock for almost every field.
The exterior clocks stopped at the exit of the balls of integer radius converge locally
uniformly with jointly measurable limits; exhausting the plane by these balls gives the
locally uniform limit of the unstopped exterior clocks, which is the remaining input of the
clock built from the half-disc and exterior parts.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The unstopped exterior clocks of the inserted field converge locally uniformly, almost
surely under the product of the field law and the Brownian law, to a jointly measurable
limit. -/
theorem exists_measurable_locally_uniform_limit_exterior_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) (x : ℂ) :
    ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
            (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - G (p,t)| < η := by
  have hstop : ∀ N : ℕ, ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal,
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η :=
    fun N => exists_measurable_locally_uniform_limit_stopped_exterior_clock_ball hh hγ hγ2 α x N
  exact exists_ae_eventually_uniform_of_stopped_balls x (fun j p u =>
      ∫ s in (0 : ℝ)..u, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
        (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
            (p.2 s.toNNReal)) hstop

/-- Existence of the LQG clock of the inserted field: for `0 < γ` with `γ ^ 2 < 2`, every
insertion `α < Q` and every start, there is a clock that is, for almost every field, an LQG
clock of planar Brownian motion for the inserted circle-average field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) := by
  have hγ2' : γ < 2 := by nlinarith
  have hext := exists_measurable_locally_uniform_limit_exterior_clock hh hγ hγ2' α x
  exact exists_ae_isLQGClock_fieldCircleAverage_of_exterior hh x hγ hγ2 hα hext

end HarmonicBalls
