import HarmonicBalls.Proofs.Sec6.GreenTranslation
import HarmonicBalls.Proofs.Sec5.LaplacianScaling
import HarmonicBalls.Proofs.SecA.Basic

/-! # Translation of distributional Laplacians

Translation preserves the test functions, the distributional pairing and
the measure-valued Laplacian. -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Laplacian
open scoped ContDiff Topology

/-- A translated test function is a test function on the translated domain. -/
theorem isTestFunction_comp_add_right {U : Set ℂ} {φ : ℂ → ℝ}
    (hφ : IsTestFunction U φ) (b : ℂ) :
    IsTestFunction ((fun z : ℂ => z + b) ⁻¹' U) (fun z => φ (z + b)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hφ.1.comp (by fun_prop)
  · exact hφ.2.1.comp_homeomorph (Homeomorph.addRight b)
  · intro z hz
    have heq := tsupport_comp_eq_preimage φ (Homeomorph.addRight b)
    exact hφ.2.2 ((Set.ext_iff.mp heq z).mp hz)

/-- Local integrability is preserved by planar translation. -/
theorem locallyIntegrableOn_comp_add_right {w : ℂ → ℝ} {U : Set ℂ}
    (hw : LocallyIntegrableOn w U) (b : ℂ) :
    LocallyIntegrableOn (fun z => w (z + b)) ((fun z : ℂ => z + b) ⁻¹' U) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight b
  intro x hx
  obtain ⟨V, hV, hi⟩ := hw (x + b) hx
  refine ⟨(fun z : ℂ => z + b) ⁻¹' V, ?_, ?_⟩
  · exact ((continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin
      (Set.mapsTo_preimage _ _)) hV
  · apply (integrableOn_map_equiv e.toMeasurableEquiv).mp
    change IntegrableOn w V (Measure.map (fun z : ℂ => z + b) volume)
    rw [map_add_right_eq_self]
    exact hi

/-- A simultaneous translation of a function and the test function leaves
the distributional Laplacian pairing unchanged. -/
theorem integral_mul_laplacian_comp_add_right (w φ : ℂ → ℝ) (b : ℂ) :
    (∫ x, w (x + b) * Δ φ x) =
      ∫ y, w y * Δ (fun z => φ (z - b)) y := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun y : ℂ => w y * Δ (fun z => φ (z - b)) y) b
  simpa only [laplacian_comp_sub_const, add_sub_cancel_right] using h

/-- The measure-valued distributional Laplacian transforms under translation
by pushing each measure forward by the inverse translation. -/
theorem hasLaplacian_comp_add_right {w : ℂ → ℝ} {μ ν : Measure ℂ} {U : Set ℂ}
    (hw : HasLaplacian w μ ν U) (b : ℂ) :
    HasLaplacian (fun z => w (z + b))
      (Measure.map (fun z => z - b) μ) (Measure.map (fun z => z - b) ν)
      ((fun z : ℂ => z + b) ⁻¹' U) := by
  refine ⟨locallyIntegrableOn_comp_add_right hw.1 b, ?_⟩
  intro φ hφ
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-b)
  have ht : IsTestFunction U (fun z => φ (z - b)) := by
    have h := isTestFunction_comp_add_right hφ (-b)
    have heq : (fun z : ℂ => z + (-b)) ⁻¹' ((fun z : ℂ => z + b) ⁻¹' U) = U := by
      ext z
      change (z + -b) + b ∈ U ↔ z ∈ U
      rw [add_assoc, neg_add_cancel, add_zero]
    rw [heq] at h
    simpa only [sub_eq_add_neg] using h
  obtain ⟨hiμ, hiν, heq⟩ := hw.2 _ ht
  refine ⟨?_, ?_, ?_⟩
  · exact (integrable_map_equiv e.toMeasurableEquiv φ).mpr (by simpa [e, sub_eq_add_neg, Function.comp_def] using hiμ)
  · exact (integrable_map_equiv e.toMeasurableEquiv φ).mpr (by simpa [e, sub_eq_add_neg, Function.comp_def] using hiν)
  · rw [integral_mul_laplacian_comp_add_right, heq]
    congr 1
    · simpa [e, sub_eq_add_neg] using (integral_map_equiv (μ := μ) e.toMeasurableEquiv φ).symm
    · simpa [e, sub_eq_add_neg] using (integral_map_equiv (μ := ν) e.toMeasurableEquiv φ).symm

end HarmonicBalls.Section6
