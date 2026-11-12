import HarmonicBalls.FirstPass.Phase2.UnitTailFieldAxioms
import HarmonicBalls.FirstPass.Phase2.UnitSquareCrossingTailDerived

/-!
# The field axioms of Fact 2.2 (derived)

The field axioms `LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2 for the field `h^ℂ - α₀ log |·|`, `α₀ < Q`:
Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Theorem 1.10, p. 10, and Proposition 3.17, p. 43) are proved:
`lqgMetricFieldAxiomsUnivFrozen_of_unitTail` derives them from the uniform tail of the unit-square crossing distances,
and that tail is `unitSquareCrossingTail_derived`. Substituting both in the counted forms gives forms of Lemmas 11.10,
11.12, 11.16 and 11.17 without literature inputs from Section 11's metric axioms, and of Lemma 11.13 at the canonical
exponent binding only the local metric replacement `hN2` and the continuity at the insertion `hfr`.

## Main statements

* `HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_derived`: Fact 2.2 (field axioms), every universe.
* `HarmonicBalls.connectedSquareUnionDiamFiniteFrozen_derived`: finite internal diameters of connected finite unions of
  closed rectangles.
* `HarmonicBalls.pinchThirdEventPositiveStmt_derived`: Lemma 11.17.
* `HarmonicBalls.firstPass_11_16_derived`: Lemma 11.16.
* `HarmonicBalls.firstPass_11_12_derived`: Lemma 11.12 (Draft form).
* `HarmonicBalls.S11c.firstPass_11_10_derived`: Lemma 11.10 (closed squares).
* `HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_derived`: Lemma 11.13 at
  the canonical exponent from `hN2` and `hfr`.
-/

universe u

namespace HarmonicBalls

/-- **Derived.** The field axioms of Fact 2.2 (`LQGMetricFieldAxiomsUnivFrozen`) in every universe. -/
theorem lqgMetricFieldAxiomsUnivFrozen_derived : LQGMetricFieldAxiomsUnivFrozen.{u} :=
  lqgMetricFieldAxiomsUnivFrozen_of_unitTail unitSquareCrossingTail_derived

/-- **Derived.** The finite internal diameters of connected finite unions of closed rectangles. -/
theorem connectedSquareUnionDiamFiniteFrozen_derived : ConnectedSquareUnionDiamFiniteFrozen.{u} :=
  connectedSquareUnionDiamFiniteFrozen_derivedUnitTail lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Draft Lemma 11.17 (`PinchThirdEventPositiveStmt`). -/
theorem pinchThirdEventPositiveStmt_derived : PinchThirdEventPositiveStmt.{u} :=
  pinchThirdEventPositiveStmt_derivedUnitTail lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Draft Lemma 11.16 (`PinchSecondEventPositiveStmt`). -/
theorem firstPass_11_16_derived : PinchSecondEventPositiveStmt.{u} :=
  firstPass_11_16_derivedUnitTail lqgMetricFieldAxiomsUnivFrozen_derived

/-- **Derived.** Lemma 11.12 (Draft form, `PinchEventPositiveProbabilityStmt`). -/
theorem firstPass_11_12_derived : PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedUnitTail lqgMetricFieldAxiomsUnivFrozen_derived

end HarmonicBalls

namespace HarmonicBalls.S11c

/-- **Derived.** Lemma 11.10 (closed-square form, `SmallMetricDiameterLargeMassSquareStmt`). -/
theorem firstPass_11_10_derived : SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedUnitTail fun γ ξ α₀ Ω _ P hC hcirc =>
    HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_derived.{u} Ω P γ ξ α₀ hC hcirc

end HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

/-- **Derived.** Lemma 11.13 at the canonical exponent (universe `0`) from the local metric replacement `hN2` and the
continuity of the rooted physical metric at the insertion `hfr`. -/
theorem firstPass_11_13_canonical_of_seedInputs_derived
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) :
    CorrectedLemma11_13CanonicalStmt.{0} :=
  firstPass_11_13_canonical_of_seedInputs_derivedUnitTail
    HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_derived.{0} hN2 hfr

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed
