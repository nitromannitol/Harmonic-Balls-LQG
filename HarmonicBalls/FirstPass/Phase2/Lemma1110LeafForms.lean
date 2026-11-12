import HarmonicBalls.FirstPass.Phase2.ConnectedSquareUnionDiamDerived
import HarmonicBalls.FirstPass.Phase2.SquarePositiveCountedForms
import HarmonicBalls.FirstPass.Phase2.Step8WholePlaneFromSeed

/-!
# Lemma 11.10 (closed squares) and Lemma 11.13 (canonical exponent) from the LQG metric inputs

* `HarmonicBalls.S11c.firstPass_11_10_derivedInputsClosedSquarePositive`: the closed-square form of Lemma 11.10
  (`S11c.firstPass_11_10_derivedInputsClosedSquare`) with the positivity of the LQG mass of closed dyadic squares
  supplied by its proof (`lqgMeasureSquarePositiveFrozen_holds`). Binders 4 → 3: `hDC`, `hSq`, `hAx`.
* `HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_metricInputs`:
  Lemma 11.13 at the canonical exponent (`firstPass_11_13_canonical_of_seedInputs_lemma11_10`) with Lemma 11.10
  supplied by `S11c.firstPass_11_10_derivedInputsSquarePositive`. The hypotheses left are inputs on the LQG metric only:
  the field axioms `hAx`, the local metric replacement `hN2`, the continuity of the rooted physical metric at the
  insertion `hfr`, the small dyadic cell diameters `hDC` and the finite internal diameters of connected unions of
  squares `hFin`.
-/

open MeasureTheory

universe u

namespace HarmonicBalls.S11c

/-- **Derived.** Lemma 11.10, closed-square form, from `hDC`, `hSq`, `hAx`: the hypothesis `hPos` of
`S11c.firstPass_11_10_derivedInputsClosedSquare` (every closed dyadic square has positive LQG mass almost surely) is
`lqgMeasureSquarePositiveFrozen_holds`. -/
theorem firstPass_11_10_derivedInputsClosedSquarePositive
    (hDC : DyadicCellDiamSmallFrozen.{u})
    (hSq : ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ Q : Set ℂ, LatticeProb.Topology.IsClosedSquare Q →
      ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ Q, ∀ v ∈ Q, internalMetric (D ω) Q u v ≤ ENNReal.ofReal A)
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedInputsClosedSquare hDC HarmonicBalls.lqgMeasureSquarePositiveFrozen_holds.{u} hSq hAx

end HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

/-- **Derived.** Lemma 11.13 at the canonical exponent from inputs on the LQG metric only: Lemma 11.10, which
`firstPass_11_13_canonical_of_seedInputs_lemma11_10` takes, is `S11c.firstPass_11_10_derivedInputsSquarePositive`
(hypotheses `hDC`, `hFin` and the field axioms `hAx`). -/
theorem firstPass_11_13_canonical_of_seedInputs_metricInputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0}) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_seedInputs_lemma11_10 hAx hN2 hfr
    (S11c.firstPass_11_10_derivedInputsSquarePositive hDC hFin
      fun γ ξ α₀ Ω _ P hC hcirc => hAx Ω P γ ξ α₀ hC hcirc)

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed
