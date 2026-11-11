import HarmonicBalls.Proofs.Sec11.SingularMetricConstantShift
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma

/-! # Normalized internal metrics from a centered field

The centered singular metric's local representation remains an explicit
hypothesis; it is not a consequence of the sigma-algebra identity alone.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A local version for the singular metric of the reference-centered field
provides a modulo-constant local version of the normalized internal metric.
The centered metric locality hypothesis is explicit. -/
theorem IsWholePlaneGFF.exists_modConst_internalMetric_of_centered_locality
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    {U V : Set ℂ} (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ)
    (hψint : ∫ x, ψ x = 1)
    (hlocal : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[fieldSigmaAlgebra α
        (fun ω => centeredTestPairing (hC ω) ψ) U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun u v =>
          (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => -hC ω ψ))) ξ
            (fun z => -α * Real.log ‖z‖) u v).toReal) V x y = G ω x y) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y) := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have hs := h.ae_internal_singularMetric_add_random_constant 𝔇 h𝔇 hD c hc
  obtain ⟨G, hG, hGeq⟩ := hlocal
  refine ⟨fun ω => Real.exp (ξ * c ω), G,
    Filter.Eventually.of_forall (fun _ => Real.exp_pos _), ?_, ?_⟩
  · intro x y
    rw [← fieldSigmaAlgebra_centeredTestPairing_eq_modConst α hC U ψ hψ hψint]
    exact hG x y
  · filter_upwards [hs, hGeq] with ω hs hg x hx y hy
    rw [internalMetric_const_mul (D ω) (Real.exp_pos _)]
    exact (hs V x y).symm.trans (hg x hx y hy)


end HarmonicBalls
