import HarmonicBalls.Proofs.Sec6.UniformGoodAnnulusFineSupport
import HarmonicBalls.Proofs.Sec6.GoodAnnulusProbabilityZeroExistence

/-! # Good-annulus probability from fine support

The imported fine-support and annulus iteration arguments use Leonardo Bonanno's
proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength
LQG existence is an input (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

universe u

/-- The frozen good-annulus probability statement follows from volume growth,
zero-strength LQG existence, and null measurability of the simultaneous dyadic
phase events. -/
theorem goodAnnulusProbabilityStmt_of_fine_support_and_phase_measurability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hmeas : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ),
      0 < γ → γ < 2 → ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ 0 hcirc μ → ∀ b ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ,
      NullMeasurableSet {ω | ∀ r ∈ Icc (1 / 2 : ℝ) 1,
        IsGoodAnnulus (μ ω) r 0 ((1 / 2 : ℝ) ^ (n + 1)) b} P) :
    GoodAnnulusProbabilityStmt.{u} := by
  apply goodAnnulusProbabilityStmt_of_dyadic_phase_and_zero_existence ?_ hE0
  intro γ hγ hγ2 b hb p hp Ω _ P hC hcirc μ h hμ
  obtain ⟨a, ha, hbound⟩ := uniform_goodAnnulus_probability_of_measurable_events
    hgrowth hγ hγ2 h hμ hb.1 hp (hmeas Ω P γ hγ hγ2 hC hcirc μ h hμ b hb)
  exact ⟨a, ha, fun r hr => hbound r ⟨hr.1.le, hr.2⟩⟩

end HarmonicBalls.Section6
