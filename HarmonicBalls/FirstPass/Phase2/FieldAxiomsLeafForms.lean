import HarmonicBalls.FirstPass.Phase2.DerivedInputs3
import HarmonicBalls.FirstPass.Phase2.DerivedInputs43

/-!
# Proposition 11.11 and Lemma 11.15 with the field axioms as the frozen input

Two counted forms of Section 11 bind the field axioms I-IV of the LQG metric (Fact 2.2) as an inline quantified
hypothesis rather than as the frozen input `LQGMetricFieldAxiomsUnivFrozen`:

* `firstPass_11_11_derivedInputs43` (`FirstPass/Phase2/DerivedInputs43.lean`, Proposition 11.11, every `ξ`) binds
  `hmetricAxioms`, the axioms on every whole-plane GFF model in `Type u`, for every `ξ` and every `α₀ < Q`;
* `firstPass_11_15_derivedInputs3` (`FirstPass/Phase2/DerivedInputs3.lean`, Lemma 11.15) binds `hFA`, the axioms on
  every model in `Type`, for every `γ`, `ξ`, `α₀`.

Both are `LQGMetricFieldAxiomsUnivFrozen` (at universe `u`, respectively `0`) with the arguments reordered and, for
`hmetricAxioms`, with redundant hypotheses added. The theorems below state the two forms with the frozen input, the one
bound by the other counted forms of Section 11.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- **Proposition 11.11 (every `ξ`), from Lemma 11.13 and the field axioms.** `firstPass_11_11_derivedInputs43` with
the field axioms of the LQG metric read off `LQGMetricFieldAxiomsUnivFrozen`. -/
theorem firstPass_11_11_fieldAxioms (h13 : ManyPinchScalesStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_derivedInputs43 h13 fun γ α₀ ξ _ _ _ Ω _ P hC hcirc _ => hAx Ω P γ ξ α₀ hC hcirc

/-- **Lemma 11.15 from the field axioms.** `firstPass_11_15_derivedInputs3` with the field axioms of the LQG metric on
probability spaces in `Type` read off `LQGMetricFieldAxiomsUnivFrozen.{0}`. -/
theorem firstPass_11_15_fieldAxioms (hAx : LQGMetricFieldAxiomsUnivFrozen.{0}) :
    PinchFirstEventPositiveStmt.{u} :=
  firstPass_11_15_derivedInputs3 fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc

end HarmonicBalls
