import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.Closure.Sec6

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

end HarmonicBalls.Closure
