import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec5.ExitTime
import HarmonicBalls.Proofs.Sec5.ExistenceFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.UniquenessFromVolumeGrowth
import HarmonicBalls.Proofs.Sec5.StrongCompatibilityAssembly
import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences
import HarmonicBalls.Proofs.Sec6.FullThreeInputAssembly
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec7.ClusterContinuity
import HarmonicBalls.Proofs.Sec8.ClusterBoundary
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.VolumeGrowthAssembly
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Steps.Sec5.ClusterBounds
import HarmonicBalls.Steps.Sec5.ContinuityAssembly

/-!
# Section 5 results from the staged measure inputs

Worker z4, task `section5-derived-staged-input-assembly`.

This module exports the Section 5 results 5.1-5.8 of Draft/Section5.lean from the three staged Proposed inputs
`WholePlaneLQGBallMassBounds` (`hDG`), `LQGMeasureCoordChange` (`hCC`) and `LQGMeasureExistence` (`hE`) of
HarmonicBalls/Proposed/LQG.lean. Those inputs were source-checked by the operator on 2026-11-08 (05:00 UTC).

Derived here, not taken as binders:
* I2, `LQGVolumeGrowthAllScalesStmt` (Draft/Section2.lean:122), from `hDG`, `hCC` at insertion `0` and `hE`
  (`lqgVolumeGrowthAllScalesStmt_of_staged_inputs`, Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53);
* Lemma 2.4, `LiouvilleVolumeGrowthStmt` (with the corrected exponent ranges [C1]), from `hDG`, `hCC` at insertion `0`
  and `hE` (`liouvilleVolumeGrowthStmt_of_existence`, Proofs/Sec9/LQGExistenceConsequences.lean:30);
* Proposition 6.1, `HarnackTypeEstimateStmt` (Draft/Section6.lean:206), from `hDG`, `hCC` at insertion `0` and `hE`
  (`Section6Full.harnackTypeEstimateStmt_of_three_inputs`, Proofs/Sec6/FullThreeInputAssembly.lean:56).

Open leaves, kept as binders under their frozen names:
* `hTyp : TypicalPointManyGoodScalesStmt` (Lemma 8.2, Draft/Section8.lean:74), used by 5.2-5.5;
* `hBT : ClusterBoundaryTouchingRightContinuityStep` (Steps/Sec5/ContinuityAssembly.lean:19; docs/campaign/GRAPH.md
  G12), used by 5.2.

Coordinate-change hypotheses. Results 5.1, 5.2, 5.3, 5.4, 5.6 and 5.8 take `hCC` at insertion `0`. Results 5.5 and 5.7
take `hCC` at every insertion; its insertion-zero restriction `coordChange_zero_of_all_insertions` feeds only the
producers of I2, Lemma 2.4 and Proposition 6.1.

Credit: Leonardo Bonanno. His potential-theoretic and LatticeProb work enters through the imported modules, which carry
his credit (for example Proofs/Sec6/FullThreeInputAssembly.lean for Proposition 6.1 and
Proofs/Sec9/WeakUniquenessDerivedInputs.lean for I2).

This is a reduction, not a numbered closure. It gives no source-fidelity verdict; the open semantic point E51 is
recorded in docs/campaign/audits/Section5StagedInputAssembly.md.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-! ## Insertion-zero coordinate change: `hDG`, `hCC` at insertion `0`, `hE` at every insertion -/

section InsertionZero

variable (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Input I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean:122), derived from the staged inputs. -/
theorem volumeGrowthI2_of_staged_inputs : LQGVolumeGrowthAllScalesStmt.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_staged_inputs hDG hCC hE

/-- Lemma 2.4 (`LiouvilleVolumeGrowthStmt`, Draft/Section2.lean:89, with the corrected exponent ranges [C1]), derived
from the staged inputs. The affine invariance and the weak-scale and non-atomicity facts of the Section 2 literature
route are proved from `hDG`, `hCC` and `hE` inside `liouvilleVolumeGrowthStmt_of_existence`. -/
theorem liouvilleVolumeGrowth_of_staged_inputs : LiouvilleVolumeGrowthStmt.{u} :=
  liouvilleVolumeGrowthStmt_of_existence hDG hCC hE

/-- Proposition 6.1 (`HarnackTypeEstimateStmt`, Draft/Section6.lean:206), derived from the staged inputs through the
full Section 6 chain. Credit: Leonardo Bonanno (annulus iteration, `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`). -/
theorem harnackTypeEstimate_of_staged_inputs : HarnackTypeEstimateStmt.{u} :=
  Section6Full.harnackTypeEstimateStmt_of_three_inputs hDG hCC hE

/-- Proposition 5.1 (`ClusterUpperBoundStmt`, Draft/Section5.lean:122) from the staged inputs. No leaf remains. -/
theorem section5_1_of_staged_inputs : ClusterUpperBoundStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC hE
  exact clusterUpperBound_of_steps
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)

/-- Proposition 5.2 (`ClusterContinuityStmt`, Draft/Section5.lean:140) from the staged inputs. Open leaves, kept as
binders: `hTyp` (Lemma 8.2) and `hBT` (the boundary-touching right-continuity step, G12). -/
theorem section5_2_of_staged_inputs (hTyp : TypicalPointManyGoodScalesStmt.{u})
    (hBT : ClusterBoundaryTouchingRightContinuityStep.{u}) : ClusterContinuityStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC hE
  exact clusterContinuity_of_boundaryTouching
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterMonotone_proved hI2)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))
    hBT

/-- Proposition 5.3 (`ClusterBoundaryMeasureZeroStmt`, Draft/Section5.lean:155) from the staged inputs. Open leaf:
`hTyp` (Lemma 8.2). -/
theorem section5_3_of_staged_inputs (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ClusterBoundaryMeasureZeroStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  exact clusterBoundaryMeasureZero_of_steps
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp)

/-- Proposition 5.4 (`RegularizedClusterHarmonicBallsStmt`, Draft/Section5.lean:175) from the staged inputs. Open leaf:
`hTyp` (Lemma 8.2). -/
theorem section5_4_of_staged_inputs (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    RegularizedClusterHarmonicBallsStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC hE
  exact regularizedClusterHarmonicBalls_of_clusterProperties (clusterOpenLaplacian_proved hI2)
    (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2)
    (section5_3_of_staged_inputs hDG hCC hE hTyp)
    (lqgMeasureFullSupportStmt_of_volumeGrowth hI2)
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))

/-- Proposition 5.6 (`UniquenessHarmonicBallsStmt`, Draft/Section5.lean:206) from the staged inputs, through I2 alone.
No leaf remains. -/
theorem section5_6_of_staged_inputs : UniquenessHarmonicBallsStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  exact uniquenessHarmonicBalls_of_boundary_and_volumeGrowth hI2
    (harmonicBallBoundarySubset_of_volumeGrowth hI2) (regularOpenEqOfAEEq_of_volumeGrowth hI2)

/-- Lemma 5.8 (`ClusterStrongCompatibilityStmt`, Draft/Section5.lean:246) from the staged inputs, through I2 alone.
The semantics of the statement over all bounded open sets are open (E51; see the audit document). -/
theorem section5_8_of_staged_inputs : ClusterStrongCompatibilityStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC hE
  exact clusterStrongCompatibilityStmt_of_volumeGrowth hI2

end InsertionZero

/-! ## All-insertion coordinate change: results 5.5 and 5.7 -/

/-- The insertion-zero restriction of an all-insertion coordinate-change input. It feeds only the producers of I2,
Lemma 2.4 and Proposition 6.1, which take insertion `0` as stated. -/
theorem coordChange_zero_of_all_insertions
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc :=
  fun _ _ P γ hC hcirc => hCC P γ 0 hC hcirc

section AllInsertions

variable (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Lemma 5.7 (`ClusterScaleInvarianceStmt`, Draft/Section5.lean:226) from the staged inputs. The coordinate-change
input is used at every insertion; the insertion-zero restriction feeds I2 only. No leaf remains. -/
theorem section5_7_of_staged_inputs : ClusterScaleInvarianceStmt.{u} := by
  have hI2 := volumeGrowthI2_of_staged_inputs hDG (coordChange_zero_of_all_insertions hCC) hE
  exact clusterScaleInvariance_of_volumeGrowth hI2 wholePlaneGFFAffineInvariance_proved hCC

/-- Theorem 5.5 (`ExistenceHarmonicBallsStmt`, Draft/Section5.lean:192) from the staged inputs. Open leaf: `hTyp`
(Lemma 8.2). The coordinate-change input is used at every insertion, as the existence step requires. -/
theorem section5_5_of_staged_inputs (hTyp : TypicalPointManyGoodScalesStmt.{u}) :
    ExistenceHarmonicBallsStmt.{u} := by
  have hCC0 := coordChange_zero_of_all_insertions hCC
  have hI2 := volumeGrowthI2_of_staged_inputs hDG hCC0 hE
  have hLiou := liouvilleVolumeGrowth_of_staged_inputs hDG hCC0 hE
  have hHarnack := harnackTypeEstimate_of_staged_inputs hDG hCC0 hE
  have h53 := section5_3_of_staged_inputs hDG hCC0 hE hTyp
  exact existenceHarmonicBalls_of_volumeGrowth_and_clusterEstimates hI2 h53
    (clusterUpperBoundPolyHighProb_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterConservationOfMass_proved hI2) hHarnack)
    (clusterTimeContinuity_of_steps hLiou (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) hHarnack
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
        (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) hTyp))
    wholePlaneGFFAffineInvariance_proved hCC

end AllInsertions

end HarmonicBalls
