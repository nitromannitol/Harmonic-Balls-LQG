import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.SingularWeylBumpLength

/-! # Zero Weyl scaling after a singular-field bump

The metric-field axioms are staged and await source check. The inverse Weyl
identity is not established here.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- Under the staged metric-field axioms, a continuous compactly supported
nonpositive bump gives a length metric whose zero Weyl scaling is itself. -/
theorem ae_singularField_weylBump_lengthMetric_zero_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) →
      let E : ℂ → ℂ → ℝ := fun x y => (weylScaling (D ω) ξ f x y).toReal
      IsEuclideanLengthMetric E ∧
        ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y) := by
  filter_upwards [ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ] with ω hω
  intro f hf hc hu
  have h := hω f hf hc hu
  exact ⟨h, h.weylScaling_zero ξ⟩

end HarmonicBalls
