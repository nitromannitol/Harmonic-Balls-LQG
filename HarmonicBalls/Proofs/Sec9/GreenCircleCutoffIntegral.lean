import HarmonicBalls.Proofs.Sec9.GreenCircleCutoffLimit

/-!
# Integrated disc Green circle averages

Monotone convergence of shrinking circle averages against a measure supported in the disc.
-/

namespace HarmonicBalls

open Metric Filter Topology Set MeasureTheory

/-- Circle averages converge in extended integral to the Green potential with an infinite
value at the pole. The measure is concentrated on the source disc. -/
theorem lintegral_circleAverage_greenFunction_ball_tendsto
    {R : ℝ} {x : ℂ} {r : ℕ → ℝ} {μ : Measure ℂ}
    (hx : x ∈ ball (0 : ℂ) R) (hμ : μ (ball (0 : ℂ) R)ᶜ = 0)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal
      (Real.circleAverage (greenFunction (ball 0 R) y) x (r n)) ∂μ) atTop
      (𝓝 (∫⁻ y, if x = y then ⊤ else ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ)) := by
  have hball : ∀ᵐ y ∂μ, y ∈ ball (0 : ℂ) R := by
    rw [ae_iff]
    exact hμ
  have hm : ∀ n, AEMeasurable (fun y => ENNReal.ofReal
      (Real.circleAverage (greenFunction (ball 0 R) y) x (r n))) μ := by
    intro n
    let f : ℂ → ℝ := fun y => -(2 * Real.pi)⁻¹ * Real.log (max (r n) ‖y - x‖) -
      greatestHarmonicMinorantBall R y x
    have hf : Measurable f := by
      dsimp [f, greatestHarmonicMinorantBall]
      fun_prop
    apply hf.ennreal_ofReal.aemeasurable.congr
    filter_upwards [hball] with y hy
    rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n)]
  apply lintegral_tendsto_of_tendsto_of_monotone hm
  · filter_upwards [hball] with y hy
    exact (circleAverage_greenFunction_ball_monotone_tendsto hx hy hr hanti hrlim hsub).1
  · filter_upwards [hball] with y hy
    exact (circleAverage_greenFunction_ball_monotone_tendsto hx hy hr hanti hrlim hsub).2

/-- A positive atom at the center makes the extended Green potential infinite. -/
theorem lintegral_extended_greenFunction_ball_eq_top_of_atom
    {R : ℝ} {x : ℂ} {μ : Measure ℂ} (hatom : μ {x} ≠ 0) :
    (∫⁻ y, if x = y then ⊤ else ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ) = ⊤ := by
  apply top_unique
  calc
    ⊤ = ∫⁻ y in {x}, if x = y then ⊤ else
        ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ := by
      rw [lintegral_singleton]
      simp [hatom]
    _ ≤ ∫⁻ y, if x = y then ⊤ else ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ :=
      lintegral_mono' Measure.restrict_le_self le_rfl

end HarmonicBalls
