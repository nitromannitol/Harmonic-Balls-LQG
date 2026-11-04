import HarmonicBalls.Proofs.Sec8.UniversalPhaseProbability
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity
import HarmonicBalls.Steps.Sec6.Prevalence

/-! # Uniform singular phase bounds from subrange prevalence -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Subrange prevalence selects the third-criterion constant before `b`, and
one-scale singular phase bounds then hold uniformly over all realizations. -/
theorem exists_uniform_singular_phase_probability_of_subrange
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ α β : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
      (2 + γ) ^ 2 / 2 < β → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∃ a ∈ Ioo (0 : ℝ) 1, ∀ δ : ℝ≥0∞, 0 < δ →
      ∃ C₁m C₁p C₂m C₂p : ℝ,
        0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
        ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
        ∀ N : ℕ, N₀ ≤ N →
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
          IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
          LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
          WholePlaneGFFAffineInvariance P hC hcirc →
          LQGMeasureCoordChange P γ 0 hC hcirc → LQGMeasureCoordChange P γ α hC hcirc →
        ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c q ∧
          AnnulusBallComparison (μ ω) 0 0 m)} ≤ δ + δ + δ + δ := by
  classical
  obtain ⟨c, hc, hprev⟩ := hsub
  refine ⟨c, hc, ?_⟩
  intro γ α β hγ hγ₂ hα hβ b hb
  obtain ⟨a, ha, hpreva⟩ := hprev γ hγ hγ₂ b hb
  refine ⟨a, ha, ?_⟩
  intro δ hδ
  by_cases hex : ∃ (Ξ : Type u) (mΞ : MeasurableSpace Ξ),
      letI := mΞ
      ∃ (P₀ : Measure Ξ) (hC₀ : Ξ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ξ → ℝ → ℂ → ℝ) (ν₀ : Ξ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀ ∧
        WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀ ∧
        LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀
  · obtain ⟨Ξ, mΞ, P₀, hC₀, hcirc₀, ν₀, h₀, hν₀, hAff₀, hCC₀⟩ := hex
    let : MeasurableSpace Ξ := mΞ
    exact exists_universal_singular_phaseVeryGoodComparable_probability hgrowth hfull P₀
      hγ hγ₂ hα hβ hc h₀ hν₀ hAff₀ hCC₀ (hpreva Ξ P₀ hC₀ hcirc₀ ν₀ h₀ hν₀)
      (measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha.1) hδ
  · refine ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num,
      9, le_rfl, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ hEx hW hAff hCC hCCα q
    exfalso
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
    exact hex ⟨Ω, mΩ, P, hC, hcirc, ν, hgff, hν, hAff, hCC⟩

#print axioms exists_uniform_singular_phase_probability_of_subrange

end HarmonicBalls
