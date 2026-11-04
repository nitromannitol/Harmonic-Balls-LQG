import HarmonicBalls.Proofs.Sec6.GoodPrevalenceGreenAssembly
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec6.GoodAnnulusGenerator

/-! # Good-annulus prevalence with the planar generator

The prevalence reduction uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess InnerProductSpace
open scoped ENNReal NNReal ContDiff ZeroAtInfty

universe u

/-- The proved planar generator identification removes that analytic premise
from the unit-circle point-avoidance reduction for good-annulus prevalence. -/
theorem goodAnnuliSubRangeStep_of_green_and_unit_circle_point_avoidance_and_planar_generator
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hunit : ∀ x : ℂ, ‖x‖ = 1 →
      ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x)
    (hsymm : ∀ x ∈ fineSupportAnnulus 0 1, ∀ y ∈ fineSupportAnnulus 0 1, x ≠ y →
      greenFunction (fineSupportAnnulus 0 1) x y = greenFunction (fineSupportAnnulus 0 1) y x)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ∂volume)
    : GoodAnnuliSubRangeStep.{u} :=
  goodAnnuliSubRangeStep_of_green_and_unit_circle_point_avoidance
    hholder hfull hgrowth hatom hAff hCC hunit hsymm
    exists_planarBrownian_generator_eq_zero_of_harmonic hC0 hCtop hsubmean

/-- Unit-circle point avoidance also suffices for the frozen good-annulus
probability statement, under the displayed analytic and LQG hypotheses. -/
theorem goodAnnulusProbabilityStmt_of_unit_circle_point_avoidance
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hunit : ∀ x : ℂ, ‖x‖ = 1 →
      ∀ᵐ p ∂(planarBrownianMotion 0), ∀ t : ℝ≥0, p t ≠ x)
    (hsymm : ∀ x ∈ fineSupportAnnulus 0 1, ∀ y ∈ fineSupportAnnulus 0 1, x ≠ y →
      greenFunction (fineSupportAnnulus 0 1) x y = greenFunction (fineSupportAnnulus 0 1) y x)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion u
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ≤
      C * ∫⁻ x in ball u (1 / 4 : ℝ), planarBrownianMotion x
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ∂volume)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  apply goodAnnulusProbabilityStmt_of_green_symmetry hholder hfull hgrowth
    hatom hAff hCC ?_ hsymm hC0 hCtop hsubmean hex hW
  intro u _ x _ hxu
  exact planarBrownianMotion_point_avoidance_of_zero
    (planarBrownianMotion_point_avoidance_zero_of_unit_circle hunit) u x hxu

end HarmonicBalls.Section6
