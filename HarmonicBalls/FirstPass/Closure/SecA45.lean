import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.S5S7S8
import HarmonicBalls.FirstPass.S6
import HarmonicBalls.FirstPass.S8d

/-!
# closures for Appendix A and Sections 4-5

For each counted numbered result X.Y of Appendix A, Section 4 and Section 5 (`docs/campaign/INVENTORY.tsv`), a theorem
`HarmonicBalls.Closure.closure_X_Y` (`closure_A_k` for Appendix A, `closure_4_k`, `closure_5_k`) whose conclusion is
exactly the conclusion of the counted `firstPass_X_Y` theorem. Every paper-owned hypothesis is discharged by its
`firstPass_*` theorem, recursively (Lemma 6.7 by `FirstPass/S6.lean:56`, Lemma 8.2 by `FirstPass/S8d.lean:32`), and the
affine-invariance Prop is discharged by its repo proof. What remains as hypotheses is only:
* Proposed inputs of `HarmonicBalls/Proposed/LQG.lean` (`hDG hCC hE hW hN`, pending source-check);
* FROZEN Props `hL1 hWeyl hE1 hE3 hB` (Lemma 8.2 route, `FirstPass/Frozen/S8c.lean`, `FirstPass/Frozen/S8d.lean`),
  taken by `closure_5_2`-`closure_5_5` only.
No cited input and no OPEN hypothesis. Proof bodies are applications only.

Appendix A (`closure_A_1`, ..., `closure_A_6`): no hypotheses.
Section 4 (`closure_4_1`, `closure_4_2`, `closure_4_3`): Proposed `hDG hCC hW hE hN`.
Section 5: `closure_5_1`, `closure_5_6`, `closure_5_7`, `closure_5_8`: Proposed `hDG hCC hE`;
`closure_5_2`-`closure_5_5`: Proposed `hDG hCC hE hW hN` and the frozen `hL1 hWeyl hE1 hE3 hB`.
In `closure_5_3`-`closure_5_5` and `closure_5_2`, `hCC` is taken in the general `(γ, α₀)` form because
`firstPass_8_2` takes it in that form (`FirstPass/S8d.lean:32`); the 0-form used by `firstPass_5_3`, `_5_4`, `_5_5`
is obtained by specialization.
-/

namespace HarmonicBalls.Closure

open MeasureTheory

universe u

/-! ## Appendix A (no hypotheses) -/

/-- **Lemma A.1** (lemma:appendix-basic-properties). No hypotheses. -/
theorem closure_A_1 : ObstacleLeastSuperharmonicMajorantStmt := firstPass_A_1

/-- **Lemma A.2** (lemma:appendix-non-coincedence-open-harmonic). No hypotheses. -/
theorem closure_A_2 : ObstacleNonCoincidenceHarmonicStmt := firstPass_A_2

/-- **Lemma A.3** (lemma:appendix-monotonicity). No hypotheses. -/
theorem closure_A_3 : ObstacleMonotoneStmt := firstPass_A_3

/-- **Lemma A.4** (lemma:appendix-zero-boundary). No hypotheses. -/
theorem closure_A_4 : ObstacleOdometerZeroBoundaryStmt := firstPass_A_4

/-- **Lemma A.5** (lemma:appendix-conservation-of-mass). No hypotheses. -/
theorem closure_A_5 : ObstacleConservationOfMassStmt := firstPass_A_5

/-- **Lemma A.6** (lemma:appendix-cluster-compatibility). No hypotheses. -/
theorem closure_A_6 : ObstacleCompatibilityStmt := firstPass_A_6

/-! ## Section 4 (hypotheses: Proposed inputs of `Proposed/LQG.lean`, affine invariance proved in the repo) -/

section Section4

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hCC hW hE hN

/-- **Proposition 4.1** (prop:lower-bound). Hypotheses: the Proposed inputs `hDG hCC hW hE hN` only. -/
theorem closure_4_1 : ClusterLowerBoundStmt.{u} := firstPass_4_1 hDG (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hW hE hN

/-- **Lemma 4.2** (odometer:cont). Hypotheses: the Proposed inputs `hDG hCC hW hE hN` only. -/
theorem closure_4_2 : LeastSupersolutionHolderStmt.{u} := firstPass_4_2 hDG (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hW hE hN

/-- **Lemma 4.3** (lemma:harmonic-ball). Hypotheses: the Proposed inputs `hDG hCC hW hE hN` only. -/
theorem closure_4_3 : ClusterSubharmonicBallStmt.{u} := firstPass_4_3 hDG (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hW hE hN

end Section4

/-! ## Lemma 8.2, the hypothesis `hTyp` of Propositions 5.2-5.5 -/

/-- Lemma 8.2 (`TypicalPointManyGoodScalesStmt`, `lemma:mu_h-doubling-and-harnack`, line 2151), discharged. It is
`HarmonicBalls.firstPass_8_2` (`FirstPass/S8d.lean:32`), whose paper-owned input Lemma 6.7 is discharged by
`HarmonicBalls.FirstPass.S6.firstPass_6_7` (`FirstPass/S6.lean:56`, from `hDG hCC hE`) and whose unnumbered input
I1 (`LQGMeasureFullSupportStmt`) is discharged by `lqgMeasureFullSupportStmt_of_literature`
(`Proofs/Sec2/Assembly.lean:124`, from the six Proposed inputs). Hypotheses: the Proposed inputs `hDG hCC hE hW hN`,
in the general `(γ, α₀)` forms that `firstPass_8_2` takes, and the five FROZEN Props `hL1 hWeyl hE1 hE3 hB`
(`FirstPass/Frozen/S8c.lean`, `FirstPass/Frozen/S8d.lean`). -/
theorem typicalPointManyGoodScales_closed
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    TypicalPointManyGoodScalesStmt.{u} :=
  firstPass_8_2 hL1
    (lqgMeasureFullSupportStmt_of_literature hDG (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN)
    hWeyl (HarmonicBalls.FirstPass.S6.firstPass_6_7 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE)
    hE hN (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc) hCC hE1 hE3 hB

/-! ## Section 5 -/

/-- Proposition 5.1 (prop:upper-bound, line 815). Hypotheses: the Proposed inputs `hDG hCC hE` only. -/
theorem closure_5_1
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterUpperBoundStmt.{u} :=
  firstPass_5_1 hDG hCC hE

/-- Proposition 5.6 (prop:uniqueness, line 872). Hypotheses: the Proposed inputs `hDG hCC hE` only. -/
theorem closure_5_6
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    UniquenessHarmonicBallsStmt.{u} :=
  firstPass_5_6 hDG hCC hE

/-- Lemma 5.7 (lemma:scale-invariance-flow, line 885). Hypotheses: the Proposed inputs `hDG hCC hE` only
(`hCC` in the general `(γ, α₀)` form of `firstPass_5_7`). -/
theorem closure_5_7
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterScaleInvarianceStmt.{u} :=
  firstPass_5_7 hDG (fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc) hE

/-- Lemma 5.8 (lemma:strong-compatibility, line 1019). Hypotheses: the Proposed inputs `hDG hCC hE` only. -/
theorem closure_5_8
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc) :
    ClusterStrongCompatibilityStmt.{u} :=
  firstPass_5_8 hDG hCC hE

/-- Proposition 5.2 (prop:continuity-of-clusters, line 2088 of the corrected draft). Hypotheses: the Proposed inputs
`hDG hCC hE hW hN`, and the five FROZEN Props `hL1 hWeyl hE1 hE3 hB` that the discharge of Lemma 8.2 needs
(`typicalPointManyGoodScales_closed`).
Scope (audit R1, MINOR HB): the conclusion `ClusterContinuityStmt` quantifies over all `t > 0` (the all-t form). It is
stronger than the printed Proposition 5.2 at line 2088, which requires `cluster z t ⋐ B₁` and writes `cluster + B_δ(z)`.
The docstring of `ClusterContinuityStmt` (Draft/Section5.lean) says the later `t` are unproved; this discrepancy is not reconciled here. -/
theorem closure_5_2
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    ClusterContinuityStmt.{u} :=
  firstPass_5_2 hDG hCC hE hW hN
    (typicalPointManyGoodScales_closed hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB)

/-- Proposition 5.3 (prop:boundary-measure, line 836). Hypotheses: as `closure_5_2`. -/
theorem closure_5_3
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    ClusterBoundaryMeasureZeroStmt.{u} :=
  firstPass_5_3 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (typicalPointManyGoodScales_closed hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB)

/-- Proposition 5.4 (prop:conditional, line 853). Hypotheses: as `closure_5_2`. -/
theorem closure_5_4
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    RegularizedClusterHarmonicBallsStmt.{u} :=
  firstPass_5_4 hDG (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hE
    (typicalPointManyGoodScales_closed hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB)

/-- Theorem 5.5 (theorem:full-theorem-minus-uniqueness, line 863). Hypotheses: as `closure_5_2`. -/
theorem closure_5_5
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) :
    ExistenceHarmonicBallsStmt.{u} :=
  firstPass_5_5 hDG (fun {Ω} _ P γ α₀ hC hcirc => hCC Ω P γ α₀ hC hcirc) hE
    (typicalPointManyGoodScales_closed hDG hCC hE hW hN hL1 hWeyl hE1 hE3 hB)

/-! ## Axiom check (repo convention, as `FirstPass/S5S7S8.lean`) -/


end HarmonicBalls.Closure
