import HarmonicBalls.Proofs.Sec6.BallMassUniformProbability
import HarmonicBalls.Proofs.Sec6.GreenUniformProbability

/-! # Uniform very-good annulus size windows

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Both size criteria have uniform probability windows at every positive
radius and every deterministic centre separated from the singularity. -/
theorem exists_universal_lqg_size_windows_all_radii
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc → ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z / (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z (ρ / 4) (2 * ρ) /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, h₁m, h₁p, h₁⟩ :=
    exists_universal_lqg_ballMassSize_window (α := α) hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hδ
  obtain ⟨C₂m, C₂p, h₂m, h₂p, h₂⟩ :=
    exists_universal_lqg_greenSize_window (α := α) hgrowth hγ hγ₂ P₀ h₀ hμ₀ hδ
  exact ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    fun Ω _ P hC hcirc μ hgff hμ hE0 ρ hρ z hz =>
      ⟨h₁ Ω P hC hcirc μ hgff hμ hE0 ρ hρ z hz,
       h₂ Ω P hC hcirc μ hgff hμ hE0 ρ hρ z hz⟩⟩

end HarmonicBalls.Section6
