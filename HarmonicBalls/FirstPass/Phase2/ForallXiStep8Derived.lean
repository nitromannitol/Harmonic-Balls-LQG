import HarmonicBalls.FirstPass.Closure.Sec11
import HarmonicBalls.FirstPass.Closure.Bridge12
import HarmonicBalls.FirstPass.Phase2.PinchScalesSeedInputsDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs47
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived

/-!
# Lemma 11.13, Proposition 11.11 and Theorem 1.2 for every `ξ` from the Step 8 identification

The corrected Lemma 11.13 (`CorrectedLemma11_13Stmt`) is `Closure.closure_11_13` from three inputs: the field axioms of
the LQG metric (`LQGMetricFieldAxiomsUnivFrozen`), the existence of the LQG measure of the whole-plane field with a
logarithmic singularity (`LQGMeasureExistence`), and the Step 8 identification of the window certificate frequency with
the probability of a Lemma 11.12 event at the insertion `γ` (`Step8IdentificationStmt`, the γ-insertion target of
`GammaZoomIdentityStmt`). The first two are theorems (`lqgMetricFieldAxiomsUnivFrozen_derived`,
`lqgMeasureExistence_forall_field`). Supplying them:

* `correctedLemma11_13_derivedStep8`: Lemma 11.13 (corrected) for every `ξ` from `Step8IdentificationStmt` alone;
* `firstPass_11_11_derivedStep8`: Proposition 11.11 for every `ξ` from the same input, through the printed Lemma 11.13
  (`Closure.manyPinchScales_of_corrected`);
* `firstPass_1_2_derivedStep8`: Theorem 1.2 for every `ξ` from the same input, through Proposition 11.11 and
  Proposition 10.7 (`firstPass_1_2_derivedInputs47`).

Statements are those of the draft; the proofs are applications.
-/

universe u

namespace HarmonicBalls

/-- **Lemma 11.13 (corrected, every `ξ`), derived** from the Step 8 identification `hStep8` alone: `Closure.closure_11_13`
with the field axioms (`lqgMetricFieldAxiomsUnivFrozen_derived`) and the existence of the LQG measure
(`lqgMeasureExistence_forall_field`) supplied. -/
theorem correctedLemma11_13_derivedStep8 (hStep8 : Step8IdentificationStmt.{u}) :
    CorrectedLemma11_13Stmt.{u} :=
  Closure.closure_11_13 lqgMetricFieldAxiomsUnivFrozen_derived lqgMeasureExistence_forall_field hStep8

/-- **Proposition 11.11 (every `ξ`), derived** from the Step 8 identification `hStep8` alone, through the corrected and
the printed Lemma 11.13. -/
theorem firstPass_11_11_derivedStep8 (hStep8 : Step8IdentificationStmt.{u}) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_derived (Closure.manyPinchScales_of_corrected (correctedLemma11_13_derivedStep8 hStep8))

/-- **Theorem 1.2 (every `ξ`), derived** from the Step 8 identification `hStep8` alone, through Proposition 11.11. -/
theorem firstPass_1_2_derivedStep8 (hStep8 : Step8IdentificationStmt.{u}) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_derivedInputs47 (firstPass_11_11_derivedStep8 hStep8)

end HarmonicBalls
