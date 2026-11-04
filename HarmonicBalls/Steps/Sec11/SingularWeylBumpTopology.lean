import HarmonicBalls.Steps.Sec11.WeylBumpTopology
import HarmonicBalls.Steps.Sec11.WeylFieldZero

/-! # Topology of a singular-field metric after a Weyl bump

The staged metric-field axioms are explicit and await source check. This
does not assert that the shifted distance satisfies the remaining metric or
length axioms, or an inverse Weyl identity.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- For the logarithmically singular field, every continuous compactly
supported nonpositive Weyl bump preserves point separation and the
Euclidean topology almost surely. -/
theorem ae_singularField_weylBump_topology_of_metricFieldAxioms
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
      (∀ x, E x x = 0) ∧ (∀ x y, E x y = 0 → x = y) ∧
      (∀ U : Set ℂ, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, E x y < ε → y ∈ U) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD,
    ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD] with ω hm hz
  intro f hf hc hu
  exact hm.weylScaling_compact_bump_topology hξ f hf hc hu hz

end HarmonicBalls
