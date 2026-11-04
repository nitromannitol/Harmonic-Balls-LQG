import HarmonicBalls.Proofs.Sec6.GoodAnnulusGreenAssembly
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator

/-! # Good-annulus probability with the planar generator discharged -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess InnerProductSpace
open scoped ENNReal NNReal ContDiff ZeroAtInfty

universe u

/-- The good-annulus statement follows from the stated LQG inputs, Green
symmetry, Brownian point avoidance and the ball submean bound. -/
theorem goodAnnulusProbabilityStmt_of_green_symmetry
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
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
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
      LQGMeasureWeylScaling P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} :=
  goodAnnulusProbabilityStmt_of_green_symmetry_and_generator hholder hfull hgrowth
    hatom hAff hCC hpolar hsymm exists_planarBrownian_generator_eq_zero_of_harmonic
    hC0 hCtop hsubmean hex hW

end HarmonicBalls.Section6
