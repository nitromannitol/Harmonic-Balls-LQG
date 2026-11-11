import HarmonicBalls.Steps.Sec11.WeylInverse
import HarmonicBalls.Steps.Sec11.SingularWeylBumpZero

/-! # Inverse Weyl scaling for singular-field metrics

The metric-field axioms used here are staged and await source check.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- Under the staged metric-field axioms, a compactly supported nonpositive
bump of the singular-field metric has a length metric representative and
satisfies the zero and inverse Weyl identities. -/
theorem ae_singularField_weylBump_identities_of_metricFieldAxioms
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
        (∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y)) ∧
        (∀ x y, ENNReal.ofReal (D ω x y) = weylScaling E ξ (fun z => -f z) x y) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_lengthMetric_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hmetric hshift
  intro f hf hc hu
  obtain ⟨c, hc⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  obtain ⟨hE, hzero⟩ := hshift f hf ‹HasCompactSupport f› hu
  exact ⟨hE, hzero, fun x y => hmetric.inverse_weylScaling hξ f hf hc hu hE x y⟩


end HarmonicBalls
