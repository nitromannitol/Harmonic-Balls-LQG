import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling

/-! # Constant shifts of a singular LQG metric

The scale factor is derived from the whole-plane LQG metric axioms. The
Weyl weight may be arbitrary, including a logarithmic singularity.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- Adding a measurable random constant to a whole-plane field multiplies its
LQG base metric by the corresponding positive exponential. -/
theorem IsWholePlaneGFF.ae_baseMetric_add_random_constant
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ u v,
      𝔇 (addFunPairing (hC ω) (fun _ => c ω)) u v =
        Real.exp (ξ * c ω) * 𝔇 (hC ω) u v := by
  have hs := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun ω _ => c ω) (fun _ => continuous_const) (fun _ => hc)
  filter_upwards [hs] with ω hs u v
  have horig : 0 ≤ 𝔇 (hC ω) u v := by
    have htri := hs.1.triangle u v u
    rw [hs.1.self_eq_zero, hs.1.symm v u] at htri
    linarith
  have hshift : 0 ≤ 𝔇 (addFunPairing (hC ω) (fun _ => c ω)) u v := by
    have htri := hs.2.1.triangle u v u
    rw [hs.2.1.self_eq_zero, hs.2.1.symm v u] at htri
    linarith
  have hw := weylScaling_add_const (𝔇 (hC ω)) ξ (c ω) 0 u v
  simp only [Pi.zero_apply, zero_add] at hw
  have heq := hs.2.2.2.1 u v
  rw [hw, hs.2.2.1 u v] at heq
  have hr := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal hshift, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_ofReal horig] at hr
  exact hr

/-- A random constant shift rescales Weyl metrics for arbitrary weights,
including the singular logarithmic weight used for LQG. -/
theorem IsWholePlaneGFF.ae_weylScaling_add_random_constant
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ (f : ℂ → ℝ) u v,
      weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ f u v =
        ENNReal.ofReal (Real.exp (ξ * c ω)) * weylScaling (𝔇 (hC ω)) ξ f u v := by
  have hs := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun ω _ => c ω) (fun _ => continuous_const) (fun _ => hc)
  filter_upwards [hs, h.ae_baseMetric_add_random_constant 𝔇 h𝔇 c hc] with ω hs heq f u v
  have hfun : 𝔇 (addFunPairing (hC ω) (fun _ => c ω)) =
      fun x y => Real.exp (ξ * c ω) * 𝔇 (hC ω) x y := by
    funext x y
    exact heq x y
  rw [hfun]
  exact hs.1.weylScaling_const_mul (Real.exp_pos _) ξ f u v

/-- The real representatives and all internal distances of a logarithmically
singular Weyl metric scale by the same random constant. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_add_random_constant
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ (U : Set ℂ) u v,
      internalMetric (fun x y =>
        (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ
          (fun z => -α * Real.log ‖z‖) x y).toReal) U u v =
        ENNReal.ofReal (Real.exp (ξ * c ω)) * internalMetric (D ω) U u v := by
  filter_upwards [h.ae_weylScaling_add_random_constant 𝔇 h𝔇 c hc, hD] with ω hs hd U u v
  have heq : (fun x y =>
      (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ
        (fun z => -α * Real.log ‖z‖) x y).toReal) =
      fun x y => Real.exp (ξ * c ω) * D ω x y := by
    funext x y
    rw [hs, ← (hd x y).2, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_ofReal (hd x y).1]
  rw [heq, internalMetric_const_mul (D ω) (Real.exp_pos _)]


end HarmonicBalls
