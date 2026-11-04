import HarmonicBalls.Steps.Sec11.MetricField
import HarmonicBalls.Steps.Sec11.WeylLocalEdges

/-! # Zero-weight identity for singular-field metrics

The identity follows from the staged metric-field proposition, whose source
check remains pending.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- The staged metric-field axioms imply that zero-weight Weyl scaling
recovers the logarithmically singular field's metric. -/
theorem ae_weylScaling_zero_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, ∀ x y, weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y) := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hmetric := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).1
  have hweyl := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).2.2.1
  filter_upwards [hmetric, hweyl, hrepr] with ω hmetric hweyl hrepr
  have heq : D ω = fun u v =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
  intro x y
  change weylScaling (D ω) ξ (fun _ => 0) x y = ENNReal.ofReal (D ω x y)
  have h := hweyl (fun _ => 0) continuous_const x y
  rw [← heq] at h
  simpa only [Pi.zero_apply, zero_sub, neg_mul, (hrepr x y).2] using h.symm

end HarmonicBalls
