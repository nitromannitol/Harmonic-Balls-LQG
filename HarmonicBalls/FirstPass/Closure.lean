import HarmonicBalls.FirstPass.Main
import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.Closure.Sec6
import HarmonicBalls.FirstPass.Closure.Sec78910

/-!
# Phase-1 closure aggregator for the counted results of "Harmonic balls in Liouville quantum gravity"

Owner: z3 (task fp-closure-main-aggregator). File `HarmonicBalls/FirstPass/Closure.lean`, namespace `HarmonicBalls.Closure`.

Convention (as in `Closure/Sec6.lean`). For a counted numbered result `X.Y`, `closure_X_Y` has the conclusion of the counted
first-pass theorem `firstPass_X_Y` (`FirstPass/*.lean`). Its hypotheses are only FIRST-PASS FROZEN Props, Proposed or
External Props, and cited Props. Every paper-owned hypothesis of the printed proof is discharged by the closure of its
result, recursively. Proof bodies are applications of the `firstPass_` theorems and of closures only.

## Table (closures in this file; the other sections are closed in their own `Closure/*.lean` modules)

| result | closure | remaining hypotheses (class) | status |
|---|---|---|---|
| 2.3 `GreenFunctionBallStmt` (prop:green-properties) | `closure_2_3` | none (unconditional) | closed |
| 3.1 `LeastSupersolutionMemStmt` (lemma:basic-properties) | `closure_3_1` | hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 3.2 `ClusterOpenLaplacianStmt` (lemma:non-coincidence-open-harmonic) | `closure_3_2` | hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 3.3 `ClusterMonotoneStmt` | `closure_3_3` | hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 3.4 `ClusterConservationOfMassStmt` | `closure_3_4` | hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 3.5 `ClusterCompatibilityStmt` (lemma:cluster-compatibility) | `closure_3_5` | hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 1.1 `ExistenceUniquenessHarmonicBallsStmt` (theorem:harmonic-balls) | `closure_1_1` | hL1, hWeyl, hE1, hE3, hB (the inputs of `closure_8_2`, `Closure/Sec78910.lean:53`, class as there); hDG, hAff, hCC, hW, hE, hN (PROPOSED) | closed |
| 1.3 `HarmonicBallLocalSetStmt` (prop:locally-determined) | `closure_1_3` | hI2 `LQGVolumeGrowthAllScalesStmt` (`Draft/Section2.lean:122`, cited input I2; **class to confirm**: a Draft-defined Prop, not in External or Proposed); hmeasure `LQGMeasureLocality` (`Proposed/LQG.lean:85`, PROPOSED); the `closure_8_2` inputs and the six Proposed Props above | closed, I2 class flagged |
| 1.2 `HarmonicBallNoveltyStmt` (theorem:harmonic-balls-properties) | not written | **OPEN**: `firstPassMain_1_2` (`Main.lean:55`) takes `h13 : ManyPinchScalesStmt` (Lemma 11.13, `Draft/Section11.lean:259`). `closure_11_13` (Sec11) concludes `CorrectedLemma11_13Stmt` (`FirstPass/S11i/Faithful.lean:80`) with an OPEN hypothesis `hStep8` (`Step8IdentificationStmt`, `FirstPass/S11i/Corrected11_13.lean:57`), and `FirstPass/S11i.lean:1-14` states 11.13 as OPEN. No bridge to `ManyPinchScalesStmt` exists. `h7` (`closure_11_7`) and `hTyp` (`closure_8_2`) are available; `hmetricAxioms` is derivable from `LQGMetricFieldAxiomsUnivFrozen` (`FirstPass/Frozen/S11j.lean:143`). | blocked on 11.13 |
| 2.5 `GreenPotentialLiouvilleHolderStmt` (prop:green-potential-holder) | none | **OPEN**: no `firstPass_2_5`. The Draft statement is FROZEN (`docs/campaign/FROZEN.md:25`). The printed proof cites Ponce 2016 Sec 16.2. The only Lean input in that role is `GreenPotentialHolderStmt` (`Draft/Section2.lean:190`), a Draft def, not an External or Proposed Prop. The ball-case Green clause exists only in the legacy `Proofs/Potential/GreenPotentialHolder.lean`. Not closed here. | OPEN |
| 4.1-4.3, A.1-A.6, 5.1-5.8 | `Closure/SecA45.lean` (z6) | not in this file; the committed file holds A and 4 only, the 5.x closures are in z6's uncommitted working copy | owner z6 |
| 6.1-6.13 except 6.5 | `Closure/Sec6.lean` (z3) | hDG, hCC, hE (PROPOSED) | closed |
| 7.1, 7.2, 8.1, 8.2, 8.3, 9.2-9.4, 10.x | `Closure/Sec78910.lean` (z7, committed 764a353) | per that file | owner z7 |
| 11.x | `Closure/Sec11.lean` (z11, partial, uncommitted edits) | per that file | owner z11 |

Cited results (2.1, 2.2, 2.4, 2.6, 6.5, 9.1 in `docs/campaign/INVENTORY.tsv`) have no closure: they are not paper-owned.
Cycles: none found. The closures used here (`closure_8_2`, `closure_11_7`, `closure_11_13`) do not refer back to Section 1.

Hypotheses of the six literature Props (the shared `variable` block of `FirstPass/S2S3S4S9SA.lean`):
* `hDG`: `WholePlaneLQGBallMassBounds` (`Proposed/LQG.lean:154`), PROPOSED, pending operator source-check.
* `hAff`: `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean:53`), PROPOSED, pending operator source-check.
* `hCC`: `LQGMeasureCoordChange` at insertion `0` (`Proposed/LQG.lean:116`), PROPOSED, pending operator source-check.
* `hW`: `LQGMeasureWeylScaling` at insertion `0` (`Proposed/LQG.lean:95`), PROPOSED, pending operator source-check.
* `hE`: `LQGMeasureExistence` at insertion `0` (`Proposed/LQG.lean:68`), PROPOSED, pending operator source-check.
* `hN`: `LQGMeasureNonatomic` (`Proposed/LQG.lean:77`), PROPOSED, pending operator source-check.

No numbered result is used as a hypothesis in this file.
-/

namespace HarmonicBalls.Closure

universe u

/-- Closure of Proposition 2.3 (`prop:green-properties`): the Green function of a ball. Unconditional. -/
theorem closure_2_3 : GreenFunctionBallStmt := firstPass_2_3

section LiteratureInputs

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
  (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
  (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)

include hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.1 (`lemma:basic-properties`): least supersolution membership. -/
theorem closure_3_1 : LeastSupersolutionMemStmt.{u} := firstPass_3_1 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.2 (`lemma:non-coincidence-open-harmonic`): the cluster is an open Laplacian set. -/
theorem closure_3_2 : ClusterOpenLaplacianStmt.{u} := firstPass_3_2 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.3: monotonicity of the cluster in the scale. -/
theorem closure_3_3 : ClusterMonotoneStmt.{u} := firstPass_3_3 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.4: conservation of mass of the cluster. -/
theorem closure_3_4 : ClusterConservationOfMassStmt.{u} := firstPass_3_4 hDG hAff hCC hW hE hN

/-- Closure of Lemma 3.5 (`lemma:cluster-compatibility`): compatibility of the clusters across scales. -/
theorem closure_3_5 : ClusterCompatibilityStmt.{u} := firstPass_3_5 hDG hAff hCC hW hE hN

end LiteratureInputs

section MainTheorems

/-- Closure of Theorem 1.1 (`theorem:harmonic-balls`): existence and uniqueness of the harmonic balls. Composition
`firstPassMain_1_1` (`FirstPass/Main.lean:33`) with Lemma 8.2 discharged by `closure_8_2` (`Closure/Sec78910.lean`). -/
theorem closure_1_1
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  firstPassMain_1_1 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN)

/-- Closure of Proposition 1.3 (`prop:locally-determined`): closed harmonic balls are local sets for the field.
Composition `firstPassMain_1_3` (`FirstPass/Main.lean:104`) with Lemma 8.2 discharged by `closure_8_2`. -/
theorem closure_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  firstPassMain_1_3 hI2 hDG hCC hE (closure_8_2 hL1 hWeyl hE1 hE3 hB hDG hAff hCC hW hE hN) hmeasure

end MainTheorems

end HarmonicBalls.Closure
