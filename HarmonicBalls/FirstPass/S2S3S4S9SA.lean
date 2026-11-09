import HarmonicBalls.Steps.Sec2.GreenFunctionBall
import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Proofs.Sec3.Assembly
import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq
import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec9.NumberedResultsAssembly
import HarmonicBalls.Proofs.SecA.Basic
import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Proofs.SecA.ObstacleMonotone
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# First pass, Sections 2, 3, 4, 9 and Appendix A (fp-S2S3S4S9SA)

Theorems `firstPass_<sec>_<num>` for the paper-owned numbered results of arXiv:2208.11795 (corrected draft) in
Sections 2, 3, 4, 9 and A. Each conclusion is the Draft statement (Draft/Section*.lean, Draft/SectionA.lean), or its
corrected form for Proposition 9.2 (`firstPass_9_2_corrected`, the weak form of [C51]).

Hypotheses are only:
* the six staged literature Props of Proposed/LQG.lean (Ding-Gwynne 2020 Lemma 3.8 as `WholePlaneLQGBallMassBounds`,
  `WholePlaneGFFAffineInvariance`, `LQGMeasureCoordChange`, `LQGMeasureWeylScaling`, `LQGMeasureExistence`,
  `LQGMeasureNonatomic`), used by the Section 3, 4, 9.3, 9.4 theorems through the Proofs/Sec2, Proofs/Sec3 and
  Proofs/Sec4 literature reductions;
* the Draft statement `TypicalPointManyGoodScalesStmt` (Draft/Section8.lean) for Proposition 9.2 weak.

Theorems with no hypotheses: `firstPass_2_3` (Prop 2.3, proved in Steps/Sec2/GreenFunctionBall.lean) and the Appendix A
lemmas. Cited results (Fact 2.1, Fact 2.2, Lemma 2.4, Prop 2.5, Prop 2.6, Lemma 9.1) have no theorem here; their Draft
statements are used as cited inputs where needed.
-/

namespace HarmonicBalls

universe u

/-- **Proposition 2.3** (prop:green-properties) — FIRST PASS. Unconditional. -/
theorem firstPass_2_3 : GreenFunctionBallStmt := greenFunctionBall

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

/-- **Lemma 3.1** (lemma:basic-properties) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_3_1 : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 3.2** (lemma:non-coincidence-open-harmonic) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_3_2 : ClusterOpenLaplacianStmt.{u} :=
  clusterOpenLaplacian_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 3.3** (lemma:monotonicity) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_3_3 : ClusterMonotoneStmt.{u} :=
  clusterMonotone_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 3.4** (lemma:conservation-of-mass) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_3_4 : ClusterConservationOfMassStmt.{u} :=
  clusterConservationOfMass_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 3.5** (lemma:cluster-compatibility) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_3_5 : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_of_literature hDG hAff hCC hW hE hN

/-- **Proposition 4.1** (prop:lower-bound) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_4_1 : ClusterLowerBoundStmt.{u} :=
  clusterLowerBound_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 4.2** (odometer:cont) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_4_2 : LeastSupersolutionHolderStmt.{u} :=
  leastSupersolutionHolder_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 4.3** (lemma:harmonic-ball) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_4_3 : ClusterSubharmonicBallStmt.{u} :=
  clusterSubharmonicBall_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 9.3** (lemma:contains-boundary) — FIRST PASS, from the six staged literature Props. -/
theorem firstPass_9_3 : HarmonicBallBoundarySubsetStmt.{u} :=
  harmonicBallBoundarySubset_of_literature hDG hAff hCC hW hE hN

/-- **Lemma 9.4** (lemma:regular-open-ae) — FIRST PASS. Its input I1 (full support of `μ_h`, an unnumbered
consequence of Lemma 2.4 and I2) is `lqgMeasureFullSupportStmt_of_literature`, from the six staged literature Props. -/
theorem firstPass_9_4 : RegularOpenEqOfAEEqStmt.{u} :=
  regularOpenEqOfAEEq (lqgMeasureFullSupportStmt_of_literature hDG hAff hCC hW hE hN)

end LiteratureInputs

section WeakUniqueness

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
  (h82 : TypicalPointManyGoodScalesStmt.{u})

include hDG hCC hW hE hN h82

/-- **Proposition 9.2**, weak form (`SubharmonicBallUniquenessWeakStmt`, [C51]) — FIRST PASS. The printed strong form
`SubharmonicBallUniquenessStmt` is false ([C51]); this is the corrected weak statement. Hypotheses: five staged literature
Props and the Draft statement `TypicalPointManyGoodScalesStmt` (Lemma 8.x, Draft/Section8.lean). -/
theorem firstPass_9_2_corrected : SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_five_staged_inputs hDG hCC hW hE hN h82

end WeakUniqueness

/-! ## Appendix A (no hypotheses) -/

/-- **Lemma A.1** (lemma:appendix-basic-properties) — FIRST PASS, unconditional. -/
theorem firstPass_A_1 : ObstacleLeastSuperharmonicMajorantStmt := obstacleLeastSuperharmonicMajorant_holds

/-- **Lemma A.2** (lemma:appendix-non-coincedence-open-harmonic) — FIRST PASS, unconditional. -/
theorem firstPass_A_2 : ObstacleNonCoincidenceHarmonicStmt := obstacleNonCoincidenceHarmonic_holds

/-- **Lemma A.3** (lemma:appendix-monotonicity) — FIRST PASS, unconditional. -/
theorem firstPass_A_3 : ObstacleMonotoneStmt := obstacleMonotone_holds

/-- **Lemma A.4** (lemma:appendix-zero-boundary) — FIRST PASS, unconditional. -/
theorem firstPass_A_4 : ObstacleOdometerZeroBoundaryStmt :=
  obstacleOdometerZeroBoundary_of_general obstacleOdometerZeroBoundaryGeneral_holds

/-- **Lemma A.5** (lemma:appendix-conservation-of-mass) — FIRST PASS, unconditional. -/
theorem firstPass_A_5 : ObstacleConservationOfMassStmt := obstacleConservationOfMass_holds

/-- **Lemma A.6** (lemma:appendix-cluster-compatibility) — FIRST PASS, unconditional. -/
theorem firstPass_A_6 : ObstacleCompatibilityStmt := obstacleCompatibility_holds

end HarmonicBalls
