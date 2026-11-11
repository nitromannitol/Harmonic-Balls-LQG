import HarmonicBalls.Assembly.ExistenceUniquenessFromEstimates
import HarmonicBalls.Proofs.Sec1.LocalityFromEstimates
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences

/-! # Section 1 from staged mass inputs

These conditional assemblies retain Propositions 6.1 and 8.1 as hypotheses.
The staged LQG predicates await source review. The potential-theoretic
infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ α hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)
  (h61 : HarnackTypeEstimateStmt.{u})
  (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u})

include hDG hCC hE h61 h81

/-- Theorem 1.1 conditional on the staged mass inputs and cluster estimates. -/
theorem existenceUniquenessHarmonicBallsStmt_of_stagedMassInputs :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  existenceUniquenessHarmonicBallsStmt_of_harnack_and_compactBoundary
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG
      (fun _ _ P γ hC hcirc => hCC P γ 0 hC hcirc) hE)
    (liouvilleVolumeGrowthStmt_of_existence hDG
      (fun _ _ P γ hC hcirc => hCC P γ 0 hC hcirc) hE)
    h61 h81 hCC

/-- The locality statement, including time zero, under the same inputs and
LQG measure locality. -/
theorem harmonicBallLocalSetStmt_of_stagedMassInputs
    (hlocal : ∀ (γ α : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α hC hcirc) : HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_harnack_and_compactBoundary
    (lqgVolumeGrowthAllScalesStmt_of_existence hDG
      (fun _ _ P γ hC hcirc => hCC P γ 0 hC hcirc) hE)
    (liouvilleVolumeGrowthStmt_of_existence hDG
      (fun _ _ P γ hC hcirc => hCC P γ 0 hC hcirc) hE)
    h61 h81 hCC hlocal


end HarmonicBalls
