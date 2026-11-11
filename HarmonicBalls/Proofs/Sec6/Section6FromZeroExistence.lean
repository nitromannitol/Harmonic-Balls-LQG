import HarmonicBalls.Proofs.Sec6.Section6FromVolumeGrowth
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Section 6 from zero-strength existence

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The coordinate-change and
existence inputs are (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory

universe u

/-- All frozen Section 6 conclusions follow from all-scales volume growth,
coordinate change and existence at zero singularity strength. -/
theorem section6_of_volumeGrowth_coordChange_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} :=
  section6_of_volumeGrowth hgrowth
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hE0

end HarmonicBalls.Section6
