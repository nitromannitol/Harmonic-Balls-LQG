import HarmonicBalls.Defs.Laplacian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Scaling facts for the distributional supersolution inequality in Section 5. -/

namespace HarmonicBalls

open MeasureTheory Laplacian
open scoped ContDiff Topology

/-- The classical Laplacian on the plane scales quadratically under a real dilation. -/
theorem laplacian_comp_real_smul (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (k : ℝ) (x : ℂ) :
    Δ (fun z => φ (k • z)) x = k ^ 2 * Δ φ (k • x) := by
  let L : ℂ →L[ℝ] ℂ := k • ContinuousLinearMap.id ℝ ℂ
  have hderiv : iteratedFDeriv ℝ 2 (fun z => φ (k • z)) x =
      (iteratedFDeriv ℝ 2 φ (k • x)).compContinuousLinearMap (fun _ => L) := by
    simpa [L, Function.comp_def] using L.iteratedFDeriv_comp_right hφ x (i := 2) le_rfl
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [hderiv, ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    smul_apply, ContinuousLinearMap.id_apply]
  have hscale (v : Fin 2 → ℂ) :
      (iteratedFDeriv ℝ 2 φ (k • x)) (fun i => k • v i) =
        k ^ 2 * (iteratedFDeriv ℝ 2 φ (k • x)) v := by
    simpa [Finset.prod_const, Fintype.card_fin, smul_eq_mul] using
      (iteratedFDeriv ℝ 2 φ (k • x)).map_smul_univ (fun _ => k) v
  rw [hscale, hscale]
  ring

/-- Pullback by a nonzero dilation preserves test functions, with their support
pulled back to the corresponding open set. -/
theorem IsTestFunction.comp_real_smul {U : Set ℂ} {φ : ℂ → ℝ}
    (hφ : IsTestFunction U φ) {k : ℝ} (hk : k ≠ 0) :
    IsTestFunction ((fun z : ℂ => k • z) ⁻¹' U) (fun z => φ (k • z)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hl : ContDiff ℝ ∞ (fun z : ℂ => k • z) := by fun_prop
    exact hφ.1.comp hl
  · exact hφ.2.1.comp_smul hk
  · intro z hz
    have hz' : k • z ∈ tsupport φ := by
      have := (tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero k hk))
      exact (Set.ext_iff.mp this z).mp hz
    exact hφ.2.2 hz'

/-- Multiplying a distributional supersolution and its measure by a positive
constant preserves the inequality. -/
theorem LaplacianLE.const_mul {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) {c : ℝ} (hc : 0 < c) :
    LaplacianLE (fun x => c * w x) (ENNReal.ofReal c • μ) U := by
  refine ⟨?_, ?_⟩
  · exact hw.1.smul c
  · intro φ hφ hφnonneg hφint
    have hi : Integrable φ μ :=
      (integrable_smul_measure (by positivity : ENNReal.ofReal c ≠ 0) ENNReal.ofReal_ne_top).mp hφint
    have h := mul_le_mul_of_nonneg_left (hw.2 φ hφ hφnonneg hi) hc.le
    simpa only [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul,
      ← integral_const_mul, mul_assoc] using h

/-- The distributional pairing with the Laplacian is invariant under a
simultaneous change of variables and pullback of the test function. -/
theorem integral_mul_laplacian_comp_smul (w φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ)
    {k : ℝ} (hk : 0 < k) :
    (∫ x, w (k • x) * Δ φ x) =
      ∫ y, w y * Δ (fun z => φ (k⁻¹ • z)) y := by
  let f : ℂ → ℝ := fun y => w y * Δ (fun z => φ (k⁻¹ • z)) y
  have hcomp : (fun x : ℂ => f (k • x)) =
      fun x => k⁻¹ ^ 2 * (w (k • x) * Δ φ x) := by
    funext x
    dsimp only [f]
    rw [laplacian_comp_real_smul φ hφ]
    simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
    ring
  have h := Measure.integral_comp_smul volume f k
  rw [hcomp, integral_const_mul] at h
  have hfactor : |(k ^ Module.finrank ℝ ℂ)⁻¹| = k⁻¹ ^ 2 := by
    rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hk _)), inv_pow]
  rw [hfactor, smul_eq_mul] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 (inv_ne_zero hk.ne')) h

/-- Local integrability on a set is preserved by the pullback under a nonzero
real dilation. -/
theorem locallyIntegrableOn_comp_real_smul {w : ℂ → ℝ} {U : Set ℂ}
    (hw : LocallyIntegrableOn w U) {k : ℝ} (hk : k ≠ 0) :
    LocallyIntegrableOn (fun z => w (k • z)) ((fun z : ℂ => k • z) ⁻¹' U) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk
  intro x hx
  obtain ⟨V, hV, hi⟩ := hw (k • x) hx
  refine ⟨(fun z : ℂ => k • z) ⁻¹' V, ?_, ?_⟩
  · exact ((continuous_const_smul k).continuousWithinAt.tendsto_nhdsWithin
      (Set.mapsTo_preimage _ _)) hV
  · apply (integrableOn_map_equiv e.toMeasurableEquiv).mp
    change IntegrableOn w V (Measure.map (fun z : ℂ => k • z) volume)
    rw [Measure.map_addHaar_smul volume hk]
    unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul]
    exact hi.smul_measure ENNReal.ofReal_ne_top

/-- The distributional Laplacian inequality is covariant under positive
real dilations, with the measure pulled back by the inverse dilation. -/
theorem LaplacianLE.comp_real_smul {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) {k : ℝ} (hk : 0 < k) :
    LaplacianLE (fun z => w (k • z))
      (Measure.map (fun z : ℂ => k⁻¹ • z) μ)
      ((fun z : ℂ => k • z) ⁻¹' U) := by
  refine ⟨locallyIntegrableOn_comp_real_smul hw.1 hk.ne', ?_⟩
  intro φ hφ hn hi
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k⁻¹ (inv_ne_zero hk.ne')
  have ht : IsTestFunction U (fun z => φ (k⁻¹ • z)) := by
    have h := hφ.comp_real_smul (inv_ne_zero hk.ne')
    have heq : (fun z : ℂ => k⁻¹ • z) ⁻¹' ((fun z : ℂ => k • z) ⁻¹' U) = U := by
      ext z
      change k • (k⁻¹ • z) ∈ U ↔ z ∈ U
      rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
    rwa [heq] at h
  have hnonneg : 0 ≤ (fun z => φ (k⁻¹ • z)) := by
    intro z
    simpa only [Pi.zero_apply] using hn (k⁻¹ • z)
  have hint : Integrable (fun z => φ (k⁻¹ • z)) μ := by
    exact (integrable_map_equiv e.toMeasurableEquiv φ).mp hi
  have hineq := hw.2 _ ht hnonneg hint
  have hφ₂ : ContDiff ℝ 2 φ := hφ.1.of_le (by simp)
  rw [integral_mul_laplacian_comp_smul w φ hφ₂ hk]
  convert hineq using 1
  exact integral_map_equiv e.toMeasurableEquiv φ

end HarmonicBalls
