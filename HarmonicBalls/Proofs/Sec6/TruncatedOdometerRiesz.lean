import HarmonicBalls.Proofs.Sec6.TruncatedOdometerLaplacian

/-! # Riesz measure of a truncated odometer

The nonnegative distributional Laplacian of the truncated odometer is a
measure; on open subsets of the selected components it dominates the original
measure. This isolates the remaining local-to-global comparison.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology Laplacian

/-- A subharmonic function whose Laplacian equals a given restricted measure
on an open subset has a Riesz measure which dominates that measure on every
open subset of the selected set. -/
theorem exists_riesz_measure_with_interior_domination
    {U Λ : Set ℂ} {v : ℂ → ℝ} {μ : Measure ℂ}
    (hU : IsOpen U) (hΛU : Λ ⊆ U) (hμ : IsLocallyFiniteMeasure μ)
    (hge : LaplacianGE v 0 U) (hΔ : HasLaplacian v (μ.restrict Λ) 0 Λ) :
    ∃ σ : Measure ℂ, σ Uᶜ = 0 ∧
      (∀ K, IsCompact K → K ⊆ U → σ K < ⊤) ∧
      (∀ φ, IsTestFunction U φ → Integrable φ σ ∧
        ∫ x, φ x ∂σ = ∫ x, v x * Δ φ x) ∧
      (∀ W, IsOpen W → W ⊆ Λ → μ W ≤ σ W) := by
  let : IsLocallyFiniteMeasure μ := hμ
  let S : (ℂ → ℝ) → ℝ := fun φ => ∫ x, v x * Δ φ x
  have hlin : IsLinearOnTests U S := by
    intro φ ψ hφ hψ a b
    exact integral_mul_laplacian_const_mul_add_const_mul hge.1 hφ hψ a b
  have hpos : IsPositiveOnTests U S := by
    intro φ hφ hφ0
    have h := (hge.2 φ hφ hφ0).2
    simpa only [integral_zero_measure] using h
  obtain ⟨σ, hσU, hσK, hσφ⟩ := exists_measure_of_isPositiveOnTests hU hlin hpos
  refine ⟨σ, hσU, hσK, hσφ, ?_⟩
  intro W hW hWΛ
  apply measure_le_of_integral_le hW
  intro φ hφ hφ01
  have hφΛ : IsTestFunction Λ φ := hφ.mono_set hWΛ
  have hφU : IsTestFunction U φ := hφΛ.mono_set hΛU
  have hiμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  obtain ⟨_, _, heq⟩ := hΔ.2 φ hφΛ
  have hrest : ∫ x in Λ, φ x ∂μ = ∫ x, φ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hφΛ.2.2 h)))
  refine ⟨hiμ, (hσφ φ hφU).1, ?_⟩
  rw [(hσφ φ hφU).2]
  change (∫ x, φ x ∂μ) ≤ ∫ x, v x * Δ φ x
  rw [heq, integral_zero_measure, sub_zero, hrest]

end HarmonicBalls.Section6
