import HarmonicBalls.Defs.LQG

/-!
# Almost sure finiteness of the LQG mass of a ball (fp-S11w; discharges `hfin` of `FirstPass/S11i/CampbellGlue.lean:36`)

The LQG measure of an `IsLQGMeasureOfField` pair is almost surely a locally finite measure (`IsLQGLimit`, `Defs/LQG.lean`).
A ball of `ℂ` has compact closure, so its mass is finite almost surely. No frozen or proposed input is used.
-/

namespace HarmonicBalls.S11w

open MeasureTheory Metric
open scoped ENNReal

/-- The LQG mass `μ_h(B_r(c))` of a Euclidean ball is almost surely finite (local finiteness of the LQG measure,
`IsLQGLimit`; Duplantier-Sheffield 2011, Prop. 1.1; the paper's Fact 2.1 I, `Defs/LQG.lean`). -/
theorem ae_measure_ball_ne_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ)
    (c : ℂ) (r : ℝ) : ∀ᵐ ω ∂P, μ ω (ball c r) ≠ ∞ := by
  filter_upwards [hμ] with ω hω
  have := hω.isLocallyFiniteMeasure
  exact (measure_ball_lt_top (μ := μ ω) (x := c) (r := r)).ne

/-- Every closed ball about the origin of radius `N` has almost surely finite LQG mass, for all `N : ℕ` at once. -/
theorem ae_forall_measure_closedBall_ne_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, μ ω (closedBall (0 : ℂ) (N : ℝ)) ≠ ∞ := by
  filter_upwards [hμ] with ω hω
  have := hω.isLocallyFiniteMeasure
  intro N
  exact (isCompact_closedBall (0 : ℂ) (N : ℝ)).measure_lt_top.ne

end HarmonicBalls.S11w
