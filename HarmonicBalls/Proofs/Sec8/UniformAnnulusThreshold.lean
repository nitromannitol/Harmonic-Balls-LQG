import HarmonicBalls.Proofs.Sec8.UniformAnnulusComparison

/-! # Uniform annulus comparison without a chosen reference realization -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The comparison threshold depends only on the field parameters and the
allowed failure probability, uniformly over realizations and dyadic scales. -/
theorem exists_lqg_annulusBallComparison_uniform_threshold
    (hfull : LQGMeasureFullSupportStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ α₀ hC hcirc →
      ∀ n, P {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} ≤ δ := by
  classical
  by_cases hex : ∃ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀),
      let _ := mΩ₀
      ∃ (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ α₀ hcirc₀ μ₀
  · obtain ⟨Ω₀, mΩ₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := hex
    let : MeasurableSpace Ω₀ := mΩ₀
    exact exists_uniform_lqg_annulusBallComparison_threshold hfull γ α₀ hγ hγ2 hα
      P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀ hδ
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Ω mΩ P hC hcirc μ h hμ _ _ n
    exact False.elim (hex ⟨Ω, mΩ, P, hC, hcirc, μ, h, hμ⟩)

end HarmonicBalls
