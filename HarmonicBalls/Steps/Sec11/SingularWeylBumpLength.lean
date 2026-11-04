import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.SingularWeylBumpMetric
import HarmonicBalls.Steps.Sec11.SingularFieldWeylForward

/-! # Length metric after a singular-field Weyl bump

The metric-field axioms are staged and await source check. The zero and
inverse Weyl identities for the shifted metric remain separate steps.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A continuous compactly supported nonpositive Weyl bump of the metric of
a logarithmically singular field is a Euclidean length metric almost surely,
under the staged metric-field axioms. -/
theorem ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) →
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_metric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hlength hmetric hfinite
  intro f hf hc hu
  obtain ⟨hdiag, hsep, hsymm, htriangle, htop⟩ := hmetric f hf hc hu
  have hscale : ∀ x y, ENNReal.ofReal ((weylScaling (D ω) ξ f x y).toReal) =
      weylScaling (D ω) ξ f x y := fun x y => (hfinite f hu x y).2
  exact ⟨hdiag, hsep, hsymm, htriangle, htop,
    hlength.weylScaling_internalMetric ξ f hscale hsymm⟩

end HarmonicBalls
