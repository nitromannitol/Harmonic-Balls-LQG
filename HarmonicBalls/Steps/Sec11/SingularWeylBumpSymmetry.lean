import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.SingularWeylBumpTopology

/-! # Symmetry of the singular-field Weyl bump

The metric-field axioms are staged and await source check. Triangle,
length and the zero and inverse Weyl identities remain separate steps.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- For a logarithmically singular field, continuous compactly supported
nonpositive Weyl bumps yield symmetric, separating distances with the
Euclidean topology almost surely. -/
theorem ae_singularField_weylBump_symmetric_topology_of_metricFieldAxioms
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
      (∀ x y, E x y = E y x) ∧
      (∀ U : Set ℂ, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, E x y < ε → y ∈ U) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_topology_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hm ht
  intro f hf hc hu
  obtain ⟨hdiag, hsep, htop⟩ := ht f hf hc hu
  refine ⟨hdiag, hsep, ?_, htop⟩
  intro x y
  exact congrArg ENNReal.toReal (hm.weylScaling_symm ξ f x y)

end HarmonicBalls
