import HarmonicBalls.Proofs.Sec3.DerivedInputAssembly
import HarmonicBalls.Proofs.Sec6.Section6FromVolumeGrowth
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs

/-! # Section 6 from three staged measure inputs: the full thirteen-result conjunction

Credit: Leonardo Bonanno. The annulus iteration of `HarmonicBalls.Section6.section6_of_volumeGrowth` is the
proved `HarmonicBalls.Section6.annulusIterationStmt_proved`, which uses his proof of the Gwynne–Miller lemma in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. This route is distinct from the Bonanno-free conditional
route `HarmonicBalls.Section6ThreeInput` (`Proofs/Sec6/ThreeInputAssembly.lean`), which is left unchanged.

Premises, in frozen order: `hDG` (whole-plane LQG ball mass bounds, `WholePlaneLQGBallMassBounds`), `hCC`
(LQG coordinate change at insertion parameter `0`, `LQGMeasureCoordChange`), and `hE` (LQG measure existence
at every insertion parameter `α`, `LQGMeasureExistence`). These are staged Proposed inputs; their source-check
by the operator is pending. The affine invariance and Weyl scaling premises of `section6_of_volumeGrowth` are
discharged by proved theorems, and the all-scales volume growth input is `lqgVolumeGrowthAllScalesStmt_of_staged_inputs`.

The exports are reductions, not numbered closure. Each typed export keeps one frozen statement by name and the
same three premises in the same order.
-/

namespace HarmonicBalls.Section6Full

open MeasureTheory

universe u

section ThreeInputs

variable (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- The thirteen frozen Section 6 statements in frozen order, from `hDG`, `hCC` and every-insertion `hE`.
Credit: Leonardo Bonanno (annulus iteration, `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`).
Reduction, not closure. -/
theorem section6Full_of_three_inputs :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} :=
  HarmonicBalls.Section6.section6_of_volumeGrowth
    (lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE)
    wholePlaneGFFAffineInvariance_univ hCC
    (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)

/-- Frozen `HarnackTypeEstimateStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem harnackTypeEstimateStmt_of_three_inputs : HarnackTypeEstimateStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).1

/-- Frozen `HarnackTypeComponentStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem harnackTypeComponentStmt_of_three_inputs : HarnackTypeComponentStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.1

/-- Frozen `ManyGoodAnnuliStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem manyGoodAnnuliStmt_of_three_inputs : ManyGoodAnnuliStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.1

/-- Frozen `GoodAnnulusProbabilityStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem goodAnnulusProbabilityStmt_of_three_inputs : GoodAnnulusProbabilityStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.1

/-- Frozen `AnnulusIterationStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno (Gwynne–Miller lemma,
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`). -/
theorem annulusIterationStmt_of_three_inputs : AnnulusIterationStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.1

/-- Frozen `ManyVeryGoodAnnuliStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem manyVeryGoodAnnuliStmt_of_three_inputs : ManyVeryGoodAnnuliStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.1

/-- Frozen `VeryGoodAnnulusProbabilityStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem veryGoodAnnulusProbabilityStmt_of_three_inputs : VeryGoodAnnulusProbabilityStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.1

/-- Frozen `AnnulusMassBoundByOdometerStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem annulusMassBoundByOdometerStmt_of_three_inputs : AnnulusMassBoundByOdometerStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.1

/-- Frozen `OdometerHarmonicMeasureBoundStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem odometerHarmonicMeasureBoundStmt_of_three_inputs : OdometerHarmonicMeasureBoundStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.2.1

/-- Frozen `OdometerBoundByAnnulusMassStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem odometerBoundByAnnulusMassStmt_of_three_inputs : OdometerBoundByAnnulusMassStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.2.2.1

/-- Frozen `VeryGoodAnnulusHarnackTypeStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem veryGoodAnnulusHarnackTypeStmt_of_three_inputs : VeryGoodAnnulusHarnackTypeStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.2.2.2.1

/-- Frozen `ShellDecompositionStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem shellDecompositionStmt_of_three_inputs : ShellDecompositionStmt :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.2.2.2.2.1

/-- Frozen `LowMassSmallOdometerStmt` from `hDG`, `hCC`, `hE`. Credit: Leonardo Bonanno. -/
theorem lowMassSmallOdometerStmt_of_three_inputs : LowMassSmallOdometerStmt.{u} :=
  (section6Full_of_three_inputs hDG hCC hE).2.2.2.2.2.2.2.2.2.2.2.2

end ThreeInputs

end HarmonicBalls.Section6Full
