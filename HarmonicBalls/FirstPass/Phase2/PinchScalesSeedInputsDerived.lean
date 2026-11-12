import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived
import HarmonicBalls.FirstPass.Phase2.Step8PerModelUniv
import HarmonicBalls.FirstPass.Phase2.NotMetricBallCanonicalLeafForms
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical

/-!
# Lemma 11.13 and Proposition 11.11 from the local metric replacement and the rooted continuity alone

The field axioms of the γ-LQG metric (`lqgMetricFieldAxiomsUnivFrozen_derived`), the small diameters of dyadic cells
(`dyadicCellDiamSmallFrozen_derived`) and the finite diameters of connected unions of squares
(`connectedSquareUnionDiamFiniteFrozen_derived`) are proved. Supplying them:

* Lemma 11.13 at the canonical exponent `ξ = γ / d_γ` holds at every universe from two inputs on the LQG metric:
  the local metric replacement (`LocalMetricReplacementStmt`) and the continuity of the rooted physical metric at the
  insertion (`RootedPhysicalMetricContinuousAtInsertionFrozen`);
* Proposition 11.11 at the canonical exponent follows from the same two inputs;
* Proposition 11.11 for every `ξ` follows from Lemma 11.13 (`ManyPinchScalesStmt`) alone.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- **Lemma 11.13 (canonical exponent, every universe), derived** from the local metric replacement `hN2` and the
continuity of the rooted physical metric at the insertion `hfr`. -/
theorem correctedLemma11_13Canonical_of_seedInputs_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  firstPass_11_13_canonical_univ_of_seedInputs_metricInputs
    lqgMetricFieldAxiomsUnivFrozen_derived lqgMetricFieldAxiomsUnivFrozen_derived.{0} hN2 hfr
    dyadicCellDiamSmallFrozen_derived.{0} connectedSquareUnionDiamFiniteFrozen_derived.{0}

/-- **Proposition 11.11 (canonical exponent), derived** from the local metric replacement `hN2` and the continuity
of the rooted physical metric at the insertion `hfr`, through Lemma 11.13 and the field axioms. -/
theorem harmonicBallNotMetricBallCanonical_of_seedInputs_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  harmonicBallNotMetricBallCanonicalStmt_of_pinch_fieldAxioms
    (Closure.manyPinchScalesCanonicalModel_of_canonical
      (correctedLemma11_13Canonical_of_seedInputs_derived hN2 hfr))
    lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Proposition 11.11 (every `ξ`), derived** from Lemma 11.13 (`ManyPinchScalesStmt`) alone. -/
theorem firstPass_11_11_derived (h13 : ManyPinchScalesStmt.{u}) : HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_fieldAxioms h13 lqgMetricFieldAxiomsUnivFrozen_derived

end HarmonicBalls
