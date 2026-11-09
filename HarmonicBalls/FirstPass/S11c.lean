import HarmonicBalls.FirstPass.S11c.Assembly110
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# First pass, Section 11, the shifted event (fp-S11c, owner n1)

Each theorem `firstPass_<sec>_<k>` concludes the Draft statement of a numbered result of Section 11
(`HarmonicBalls/Draft/Section11.lean`). Its hypotheses are Draft statements, EXTERNAL frozen Props of
`FirstPass/Frozen/S11c.lean` and `FirstPass/Frozen/*`, and the staged `Proposed/` inputs (operator ruling 19:45 UTC).

* Proposition 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, Draft/Section11.lean:214): `firstPass_11_10`, paper
  lemma:mass-diam (lines 3071-3112) and the proof of Proposition 11.10 (`prop:mass-diam-gen`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- FIRST-PASS, Proposition 11.10 (`SmallMetricDiameterLargeMassSquareStmt`, Draft/Section11.lean:214). For closed dyadic
squares `S₁ ⊆ S₂` with `S₂` disjoint from the unit circle and `C > ε > 0`, the event that the internal diameter of `S₂`
is at most `ε` and the mass of `S₁` is at least `C` has a measurable subset of positive probability.

Hypotheses: the frozen Props `DyadicCellDiamSmallFrozen`, `CameronMartinEventTransferFrozen`,
`LQGMeasureSquarePositiveFrozen`, `LQGMeasureSquareMeasurableFrozen`, `LQGMetricSupMeasurableFrozen`,
`ConnectedSquareUnionDiamFiniteFrozen`, `WeylInternalClosedFrozen`, `LQGMetricContinuousShiftFactI`, and the measurability
of the Weyl-shifted metric and measure `WeylShiftedSupMeasurableFrozen`, `WeylShiftedMassMeasurableFrozen` (operator ruling
19:45 UTC, item n1 (1)); and the staged Proposed field axioms `LQGMetricFieldAxioms`, quantified over the field objects
(operator ruling 19:45 UTC, item n1 (2)). -/
theorem firstPass_11_10.{u}
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen) (hFactI : LQGMetricContinuousShiftFactI.{u})
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} := by
  intro γ α₀ ξ hγ hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD S₁ S₂ hS₁ hS₂ hS12 hdisj C ε hε hεC
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  exact shifted_event_pos_11_10 hγ hγ2 hα P hGFF hμ hD (hAx γ ξ α₀ Ω P hC hcirc) hS₁ hS₂ hS12 hdisj
    hε hεC hDC hCM hPos hMassM hSupM hFin hW hFactI
    (fun f hf1 hf2 hf3 => hM1 γ α₀ ξ hγ hγ2 hα Ω P hC hcirc μ D hGFF hμ hD f hf1 hf2 hf3 S₂ hS₂)
    (fun f hf1 hf2 hf3 => hM2 γ α₀ ξ hγ hγ2 hα Ω P hC hcirc μ D hGFF hμ hD f hf1 hf2 hf3 S₁ hS₁)

#print axioms firstPass_11_10

end HarmonicBalls.S11c
