import HarmonicBalls.FirstPass.Phase2.DerivedInputs45
import HarmonicBalls.FirstPass.Phase2.DerivedInputs46

/-!
# Derived-input forms, round 47: Proposition 10.7 supplied to Theorem 1.2

Each theorem below is the declaration named in its docstring with the hypothesis `hjordan`
(`HarmonicBallComplementBoundaryJordanStmt`, Proposition 10.7) removed: Proposition 10.7 is now a
theorem without hypotheses, `Closure.closure_10_7_derivedInputs46` (from Torhorst's theorem on
simple-loop frontiers). Statements are otherwise copied verbatim; the proofs are applications.
-/

universe u

namespace HarmonicBalls

/-- `HarmonicBallNoveltyStmt` (Theorem 1.2) from `firstPass_1_2_derivedInputs43`, with Proposition 10.7
(`HarmonicBallComplementBoundaryJordanStmt`, `Closure.closure_10_7_derivedInputs46`) supplied.
The one remaining hypothesis is Proposition 11.11. -/
theorem firstPass_1_2_derivedInputs47
    (hmetric : HarmonicBallNotMetricBallStmt.{u}) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_derivedInputs43.{u} (hjordan := Closure.closure_10_7_derivedInputs46.{u})
    (hmetric := hmetric)

/-- `HarmonicBallNoveltyCanonicalStmt` (Theorem 1.2 at `ξ = lqgXi γ`) from
`harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs45`, with Proposition 10.7
(`HarmonicBallComplementBoundaryJordanStmt`, `Closure.closure_10_7_derivedInputs46`) supplied.
The one remaining hypothesis is Proposition 11.11 at the canonical exponent. -/
theorem harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs47
    (hmetric : HarmonicBallNotMetricBallCanonicalStmt.{u}) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs45.{u}
    (hjordan := Closure.closure_10_7_derivedInputs46.{u}) (hmetric := hmetric)

end HarmonicBalls
