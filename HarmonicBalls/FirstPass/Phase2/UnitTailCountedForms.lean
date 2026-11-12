import HarmonicBalls.FirstPass.Phase2.Lemma1110LeafForms
import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos
import HarmonicBalls.FirstPass.Phase2.DyadicCellDiamSmallNearZero
import HarmonicBalls.FirstPass.Phase2.ClosedSquareDiamNearZero

/-!
# Lemmas 11.10, 11.12, 11.13, 11.16 and 11.17 from the field axioms and the unit-square crossing tail

Two inputs on the LQG metric of the counted forms of Section 11 are consequences of the field axioms `hAx` and of one
further input, the uniform tail of the unit-square crossing distances `hUniv`: for every `γ ∈ (0, 2)` and every
`γ`-LQG metric `𝔇` with exponent `ξ` there are `δ < ξ (Q - 2) log 2` and a sequence `p` with `∑ 4^n p n < ∞` such that,
for every whole-plane GFF, the probability that the unit square `[0, 1]²` has no `D_h`-short half-crossings at level
`e^{δ n}` is at most `p n` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.1, and the
proof of Proposition 3.17, pp. 43-44).

* the small internal diameters of the clipped enlarged dyadic cells, `DyadicCellDiamSmallFrozen`, is
  `dyadicCellDiamSmallFrozen_of_unitTail_derived` (positivity of `ξ` and `hUniv`);
* the finite internal diameters of connected finite unions of closed rectangles,
  `ConnectedSquareUnionDiamFiniteFrozen`, is `connectedSquareUnionDiamFiniteFrozen_of_unitTail_derived`
  (`hAx`, positivity of `ξ` and `hUniv`).

The positivity of `ξ` is `isLQGMetric_xi_pos`. Substituting these two theorems in the forms binding
`hDC hFin hAx` gives forms binding `hAx` and `hUniv` only.

## Main statements

* `HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_xiPos`,
  `HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos`
* `HarmonicBalls.S11c.firstPass_11_10_derivedInputsUnitTail`: Lemma 11.10 (closed squares).
* `HarmonicBalls.pinchThirdEventPositiveStmt_derivedInputsUnitTail`: Lemma 11.17.
* `HarmonicBalls.firstPass_11_16_derivedInputsUnitTail`: Lemma 11.16.
* `HarmonicBalls.firstPass_11_12_derivedInputsUnitTail`: Lemma 11.12.
* `HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_unitTail`:
  Lemma 11.13 at the canonical exponent (universe `0`), from `hAx`, `hN2`, `hfr` and `hUniv`.
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace HarmonicBalls

/-- **Derived.** The small internal diameters of the clipped enlarged dyadic cells from the unit-square crossing tail
alone: `dyadicCellDiamSmallFrozen_of_unitTail_derived` with the positivity of `ξ` supplied by `isLQGMetric_xi_pos`. -/
theorem dyadicCellDiamSmallFrozen_of_unitTail_xiPos
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    DyadicCellDiamSmallFrozen.{u} :=
  dyadicCellDiamSmallFrozen_of_unitTail_derived isLQGMetric_xi_pos hUniv

/-- **Derived.** The finite internal diameters of connected finite unions of closed rectangles from the field axioms
and the unit-square crossing tail: `connectedSquareUnionDiamFiniteFrozen_of_unitTail_derived` with the positivity of
`ξ` supplied by `isLQGMetric_xi_pos`. -/
theorem connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    ConnectedSquareUnionDiamFiniteFrozen.{u} :=
  connectedSquareUnionDiamFiniteFrozen_of_unitTail_derived hAx isLQGMetric_xi_pos hUniv

/-- **Derived.** Draft Lemma 11.17 (`PinchThirdEventPositiveStmt`, every real `ξ`) from the field axioms and the
unit-square crossing tail: `pinchThirdEventPositiveStmt_derivedInputsMetric` with `hDC` and `hFin` supplied by
`dyadicCellDiamSmallFrozen_of_unitTail_xiPos` and `connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos`. -/
theorem pinchThirdEventPositiveStmt_derivedInputsUnitTail
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventPositiveStmt.{u} :=
  pinchThirdEventPositiveStmt_derivedInputsMetric (dyadicCellDiamSmallFrozen_of_unitTail_xiPos hUniv)
    (connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos hAx hUniv) hAx

/-- **Derived.** Draft Lemma 11.16 (`PinchSecondEventPositiveStmt`) from the field axioms and the unit-square
crossing tail (`firstPass_11_16_derivedInputsMetric`). -/
theorem firstPass_11_16_derivedInputsUnitTail
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchSecondEventPositiveStmt.{u} :=
  firstPass_11_16_derivedInputsMetric (dyadicCellDiamSmallFrozen_of_unitTail_xiPos hUniv)
    (connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos hAx hUniv) hAx

/-- **Derived.** Lemma 11.12 (Draft form) from the field axioms and the unit-square crossing tail
(`firstPass_11_12_derivedInputsMetric`). -/
theorem firstPass_11_12_derivedInputsUnitTail
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedInputsMetric (dyadicCellDiamSmallFrozen_of_unitTail_xiPos hUniv)
    (connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos hAx hUniv) hAx

end HarmonicBalls

namespace HarmonicBalls.S11c

/-- **Derived.** Lemma 11.10 (closed-square form, `SmallMetricDiameterLargeMassSquareStmt`) from the field axioms
and the unit-square crossing tail: `firstPass_11_10_derivedInputsSquarePositive` with `hDC` and `hFin` supplied by
`dyadicCellDiamSmallFrozen_of_unitTail_xiPos` and `connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos`. -/
theorem firstPass_11_10_derivedInputsUnitTail
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedInputsSquarePositive (HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_xiPos hUniv)
    (HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos
      (fun Ω _ P γ ξ α₀ hC hcirc => hAx γ ξ α₀ Ω P hC hcirc) hUniv) hAx

end HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

/-- **Derived.** Lemma 11.13 at the canonical exponent (universe `0`) from the field axioms `hAx`, the local metric
replacement `hN2`, the continuity of the rooted physical metric at the insertion `hfr` and the unit-square crossing
tail `hUniv`: `firstPass_11_13_canonical_of_seedInputs_metricInputs` with `hDC` and `hFin` supplied by
`dyadicCellDiamSmallFrozen_of_unitTail_xiPos` and `connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos`. -/
theorem firstPass_11_13_canonical_of_seedInputs_unitTail
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_seedInputs_metricInputs hAx hN2 hfr
    (HarmonicBalls.dyadicCellDiamSmallFrozen_of_unitTail_xiPos hUniv)
    (HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_of_unitTail_xiPos hAx hUniv)

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed
