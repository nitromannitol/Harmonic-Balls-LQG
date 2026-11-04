import HarmonicBalls.Proposed.LQG

/-!
# The singular-field metric hypothesis

This isolates the metric consequence of the staged literature proposition for use
in the deterministic argument of Lemma 11.14. The proposition is an explicit
hypothesis and has not been source-checked here.
-/

namespace HarmonicBalls

open MeasureTheory Filter

/-- The staged metric-field proposition gives the length-metric property of the
actual representative `D`, using its nonnegativity and Weyl-scaling identity. -/
theorem ae_isEuclideanLengthMetric_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hmetric := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).1
  filter_upwards [hmetric, hrepr] with ω hmetric hrepr
  have heq : D ω = fun u v =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
  rw [heq]
  exact hmetric.2

end HarmonicBalls
