import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.FiniteApproximantBallBound
import LatticeProb.LQG.LQGWeylScaling

/-!
# Finite families of singular approximation masses

Finite families of dyadic approximations admit quadratic ball mass bounds on
bounded sets of centers.
-/

open MeasureTheory Filter Metric

namespace HarmonicBalls

/-- On one full-measure event, each finite family of singular dyadic
approximations has a common quadratic ball bound on bounded sets of centers. -/
theorem ae_singular_approximant_finite_ball_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ (N : ℕ) (R : ℝ), ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ∀ k < N, lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)
          (ball z r) ≤ ENNReal.ofReal (C * r ^ 2) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr fun k =>
      LatticeProb.LQG.LQGWeylScalingDerived.ae_continuous_fieldCircleAverage_of_isWholePlaneGFF
        hlp α (by unfold dyadicScale; positivity)
  filter_upwards [hc] with ω hω N R
  exact LatticeProb.LQG.exists_finite_lqgApprox_ball_le γ
    (fieldCircleAverage α (hcirc ω)) dyadicScale N (fun k _ => hω k) R

end HarmonicBalls
