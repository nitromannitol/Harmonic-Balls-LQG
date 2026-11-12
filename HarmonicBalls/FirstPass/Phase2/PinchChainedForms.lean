import HarmonicBalls.FirstPass.Phase2.DerivedInputs44
import HarmonicBalls.FirstPass.Phase2.SquarePositiveCountedForms
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs

/-!
# Proposition 11.9, Proposition 11.16 and Lemma 11.17 from the metric inputs alone

The counted forms of Proposition 11.9 (`firstPass_11_9_derivedInputsFieldAxioms`, hypotheses `hAx`, `h1110`),
Proposition 11.16 (`firstPass_11_16_corrected_derivedInputs44`, hypotheses `hAx`, `hD`) and Lemma 11.17
(`firstPass_11_17_corrected_derivedInputs44`, hypotheses `h16`, `hAx`) bind statements proved in the paper itself:
`h1110` is Lemma 11.10, `hD` is Proposition 11.9 and `h16` is Proposition 11.16. Composing them with the closed-square
form of Lemma 11.10 (`S11c.firstPass_11_10_derivedInputsSquarePositive`, hypotheses `hDC`, `hFin`, `hAx`) gives the
three results from the LQG metric inputs alone: the field axioms `hAx` of the LQG metric, the smallness of the
internal diameters of the dyadic cells `hDC`, and the finiteness of the internal diameters of connected unions of
squares `hFin`.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Proposition 11.9 (small LQG-metric diameter and large LQG mass with positive probability) from the LQG metric
inputs `hDC`, `hFin`, `hAx`: Lemma 11.10 is supplied by its closed-square form. -/
theorem firstPass_11_9_derivedInputsMetric
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    SmallMetricDiameterLargeMassStmt.{u} :=
  firstPass_11_9_derivedInputsFieldAxioms (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)
    (S11c.firstPass_11_10_derivedInputsSquarePositive hDC hFin
      (fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc))

/-- Proposition 11.16 (corrected form) from the LQG metric inputs `hDC`, `hFin`, `hAx`: Proposition 11.9 is
supplied by `firstPass_11_9_derivedInputsMetric`. -/
theorem firstPass_11_16_corrected_derivedInputsMetric
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_derivedInputs44 hAx (firstPass_11_9_derivedInputsMetric hDC hFin hAx)

/-- Lemma 11.17 (corrected form) from the LQG metric inputs `hDC`, `hFin`, `hAx`: Proposition 11.16 is supplied by
`firstPass_11_16_corrected_derivedInputsMetric`. -/
theorem firstPass_11_17_corrected_derivedInputsMetric
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventFaithfulStmt.{u} :=
  firstPass_11_17_corrected_derivedInputs44 (firstPass_11_16_corrected_derivedInputsMetric hDC hFin hAx) hAx

end HarmonicBalls
