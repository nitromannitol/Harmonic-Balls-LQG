import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne
/-! # Completed generation of the punctured whole-plane field

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory Set Metric Filter Laplacian
open scoped Topology
namespace HarmonicBalls
/-- Punctured Laplacian pairings generate the whole-plane field modulo constants
up to completion of the probability measure. -/
theorem IsWholePlaneGFF.completed_punctured_laplacian_generation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) :
    ∀ A : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC univ] A →
      ∃ B : Set Ω, MeasurableSet[puncturedLaplacianSigma hC] B ∧ A =ᵐ[P] B := by
  apply completed_field_generation_of_laplacian_approximation P hC α₀
  intro φ hφ hzero
  obtain ⟨ψ, hψ, hcov⟩ := h.punctured_laplacian_covariance_approximation φ hφ hzero
  exact ⟨ψ, hψ, h.tendstoInMeasure_pairing_of_covariance_error φ hφ
    (fun k => Δ (ψ k)) (fun k => (hψ k).2.1) hcov⟩
end HarmonicBalls
