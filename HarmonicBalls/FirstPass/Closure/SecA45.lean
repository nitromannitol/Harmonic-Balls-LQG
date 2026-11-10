import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.FirstPass.S5S7S8

/-!
# First-pass closures for Appendix A and Sections 4-5 (task fp-closure-A45, worker z6)

For each counted numbered result X.Y of Appendix A, Section 4 and Section 5 (`docs/campaign/INVENTORY.tsv`), a theorem
`HarmonicBalls.Closure.closure_X_Y` (`closure_A_k` for Appendix A) whose conclusion is exactly the conclusion of the
counted `firstPass_X_Y` theorem. Its hypotheses are only Proposed inputs of `HarmonicBalls/Proposed/LQG.lean` (pending
operator source-check) and the cited Draft statements named in the docstring of each theorem. Proof bodies are
applications only.

Appendix A (`closure_A_1`, ..., `closure_A_6`): no hypotheses.
Section 4 (`closure_4_1`, `closure_4_2`, `closure_4_3`): the six Proposed inputs.
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

/-! ## Section 4 (hypotheses: the six Proposed inputs of `Proposed/LQG.lean`) -/

section Section4

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

/-- **Proposition 4.1** (prop:lower-bound). Hypotheses: the six Proposed inputs only. -/
theorem closure_4_1 : ClusterLowerBoundStmt.{u} := firstPass_4_1 hDG hAff hCC hW hE hN

/-- **Lemma 4.2** (odometer:cont). Hypotheses: the six Proposed inputs only. -/
theorem closure_4_2 : LeastSupersolutionHolderStmt.{u} := firstPass_4_2 hDG hAff hCC hW hE hN

/-- **Lemma 4.3** (lemma:harmonic-ball). Hypotheses: the six Proposed inputs only. -/
theorem closure_4_3 : ClusterSubharmonicBallStmt.{u} := firstPass_4_3 hDG hAff hCC hW hE hN

end Section4

end HarmonicBalls.Closure
