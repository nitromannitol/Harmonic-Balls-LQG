import HarmonicBalls.FirstPass.Phase2.DerivedInputs43

/-!
# Proposition 11.11 (canonical exponent) from Lemma 11.13 and the field axioms

`harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43`
(`FirstPass/Phase2/DerivedInputs43.lean`) proves `HarmonicBallNotMetricBallCanonicalStmt` (Proposition 11.11 with
`ξ = lqgXi γ`) from two hypotheses: `hmany : Closure.ManyPinchScalesCanonicalModelStmt` (the many pinch scales of
Lemma 11.13 on the canonical model), and `hmetricAxioms`, the field axioms I-IV of the LQG metric (Fact 2.2) on every
whole-plane GFF model, for every `ξ` and every insertion exponent `α₀ < Q`. The hypothesis `hmetricAxioms` is the
frozen input `LQGMetricFieldAxiomsUnivFrozen` with its arguments reordered. The theorem below states the form with
that frozen input, the one bound by the other counted forms of Section 11.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- **Proposition 11.11 (canonical exponent), from Lemma 11.13 and the field axioms.**
`harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43` with the field axioms
of the LQG metric read off `LQGMetricFieldAxiomsUnivFrozen`. -/
theorem harmonicBallNotMetricBallCanonicalStmt_of_pinch_fieldAxioms
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43 hmany
    fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc

end HarmonicBalls
