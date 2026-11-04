import HarmonicBalls.Proofs.Sec11.PuncturedMetricOriginExtension
import HarmonicBalls.Steps.Sec11.PunctureCrossing

/-! # Singular metric locality from small puncture detours

The Section 8 inputs use Leonardo Bonanno's LatticeProb code. The small
punctured internal-distance condition is an explicit assumption.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal NNReal

/-- If punctured internal distances vanish uniformly near the origin, then
the normalized singular internal metric has a local representative on the
entire open domain. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_small_detours
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hsmall : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ a b : ℂ, a ∈ V → b ∈ V → a ≠ 0 → b ≠ 0 → ‖a‖ < r → ‖b‖ < r →
        internalMetric (D ω) (V \ {0}) a b < ε) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y := by
  apply h.exists_modConst_internal_singularMetric_of_point_removal
    𝔇 h𝔇 hD hmetric hV hne hVU ψ hψ hψint
  filter_upwards [hmetric, hsmall] with ω hω hs x hx y hy
  have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hy0 : y ≠ 0 := by simpa only [mem_singleton_iff] using hy.2
  exact hω.internalMetric_sdiff_zero_eq_of_small_detours hx0 hy0 hs

#print axioms IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_small_detours

end HarmonicBalls
