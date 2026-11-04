import HarmonicBalls.Steps.Sec11.WeylFieldZero
import HarmonicBalls.Steps.Sec11.WeylScalingOrder

/-! # Forward Weyl identity for the logarithmically singular field

This uses the staged metric-field axioms; their source check is pending.
It does not assert finiteness or the length property of the shifted metric.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- For a logarithmically singular field, the staged Weyl axiom identifies
continuous Weyl shifts of its metric with shifts of the whole-plane metric. -/
theorem ae_weylScaling_singularField_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hrepr : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ x y,
      weylScaling (D ω) ξ f x y =
        weylScaling (𝔇 (hC ω)) ξ (fun z => f z - α₀ * Real.log ‖z‖) x y := by
  have hweyl := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).2.2.1
  filter_upwards [hweyl, hrepr] with ω hweyl hrepr
  have heq : D ω = fun u v =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
  intro f hf x y
  have h := hweyl f hf x y
  rw [← heq] at h
  exact h.symm

/-- A nonpositive Weyl weight produces finite distances for the singular-field
metric, and its real-valued representative has the forward Weyl identity. -/
theorem ae_singularField_negative_weylScaling_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, (∀ z, f z ≤ 0) → ∀ u v,
      weylScaling (D ω) ξ f u v < ∞ ∧
      ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) =
        weylScaling (D ω) ξ f u v := by
  filter_upwards [ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD] with ω hzero
  intro f hf u v
  have hle : weylScaling (D ω) ξ f u v ≤ weylScaling (D ω) ξ 0 u v := by
    apply weylScaling_mono_exponent
    intro z
    simpa using mul_nonpos_of_nonneg_of_nonpos hξ (hf z)
  rw [hzero u v] at hle
  have hfinite : weylScaling (D ω) ξ f u v < ∞ :=
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  exact ⟨hfinite, ENNReal.ofReal_toReal hfinite.ne⟩

end HarmonicBalls
