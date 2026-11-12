import HarmonicBalls.FirstPass.Phase2.UnitTailCountedForms
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsUniv
import HarmonicBalls.FirstPass.LPBridge.M5b
import LatticeProb.LQG.LQGMetricFieldAxiomsOfHalfCrossings

/-!
# The field axioms of Fact 2.2 from the unit-square crossing tail

The field axioms `LQGMetricFieldAxiomsUnivFrozen` (Fact 2.2 for the field `h^ℂ - α₀ log |·|`, `α₀ < Q`:
Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Theorem 1.10, p. 10, and Proposition 3.17, p. 43) follow from
the uniform tail of the unit-square crossing distances `hUniv` (loc. cit., Proposition 3.1, p. 13, and the union bound
of the proof of Proposition 3.10): for every `γ ∈ (0, 2)` and every `γ`-LQG metric `𝔇` with exponent `ξ` there are
`δ < ξ (Q - 2) log 2` and `p` with `∑ 4^n p n < ∞` such that, for every whole-plane GFF, the probability that `[0, 1]²`
has no `D_h`-short half crossings at level `e^{δ n}` is at most `p n`. The four axioms are proved in
`LatticeProb.LQG.lqgMetricFieldAxioms_of_halfCrossings` on `Type`; the passage to every universe is
`lqgMetricFieldAxiomsUnivFrozen_of_zero`.

Substituting this in the forms of `UnitTailCountedForms.lean`, which bind `hAx` and `hUniv`, gives forms binding
`hUniv` only (and `hN2`, `hfr` for Lemma 11.13 at the canonical exponent).

## Main statements

* `HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_of_unitTail`: `hAx` from `hUniv`.
* `HarmonicBalls.S11c.firstPass_11_10_derivedInputsUnitTailOnly`: Lemma 11.10 (closed squares).
* `HarmonicBalls.firstPass_11_12_derivedInputsUnitTailOnly`: Lemma 11.12.
* `HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed.firstPass_11_13_canonical_of_seedInputs_unitTailOnly`:
  Lemma 11.13 at the canonical exponent (universe `0`).
* `HarmonicBalls.firstPass_11_16_derivedInputsUnitTailOnly`: Lemma 11.16.
* `HarmonicBalls.pinchThirdEventPositiveStmt_derivedInputsUnitTailOnly`: Lemma 11.17.
-/

open MeasureTheory
open scoped ENNReal

universe u

namespace HarmonicBalls

/-- **Derived.** The field axioms of Fact 2.2 (`LQGMetricFieldAxiomsUnivFrozen`, every universe) from the uniform
unit-square crossing tail `hUniv`: `LatticeProb.LQG.lqgMetricFieldAxioms_of_halfCrossings` on `Type`, transported by
`LPBridge.lqgMetricFieldAxioms_iff`, `LPBridge.isLQGMetric_iff` and `LPBridge.isWholePlaneGFF_iff`, then
`lqgMetricFieldAxiomsUnivFrozen_of_zero`. -/
theorem lqgMetricFieldAxiomsUnivFrozen_of_unitTail
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    LQGMetricFieldAxiomsUnivFrozen.{u} := by
  refine lqgMetricFieldAxiomsUnivFrozen_of_zero ?_
  intro Ω _ P γ ξ α₀ hC hcirc
  refine (LPBridge.lqgMetricFieldAxioms_iff P γ ξ α₀ hC hcirc).mpr
    (LatticeProb.LQG.lqgMetricFieldAxioms_of_halfCrossings fun hγ hγ2 𝔇 h𝔇 => ?_)
  obtain ⟨δ, hδ, p, hp, huniv⟩ := hUniv γ ξ 𝔇 hγ hγ2 ((LPBridge.isLQGMetric_iff γ ξ 𝔇).mpr h𝔇)
  exact ⟨δ, p, hδ, fun hC' hcirc' hG' n =>
    huniv Ω P hC' hcirc' ((LPBridge.isWholePlaneGFF_iff P hC' hcirc').mpr hG') n, hp⟩

/-- **Derived.** Lemma 11.17 (`PinchThirdEventPositiveStmt`) from the unit-square crossing tail alone. -/
theorem pinchThirdEventPositiveStmt_derivedInputsUnitTailOnly
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    PinchThirdEventPositiveStmt.{u} :=
  pinchThirdEventPositiveStmt_derivedInputsUnitTail hUniv (lqgMetricFieldAxiomsUnivFrozen_of_unitTail hUniv)

/-- **Derived.** Lemma 11.16 (`PinchSecondEventPositiveStmt`) from the unit-square crossing tail alone. -/
theorem firstPass_11_16_derivedInputsUnitTailOnly
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    PinchSecondEventPositiveStmt.{u} :=
  firstPass_11_16_derivedInputsUnitTail hUniv (lqgMetricFieldAxiomsUnivFrozen_of_unitTail hUniv)

/-- **Derived.** Lemma 11.12 (Draft form, `PinchEventPositiveProbabilityStmt`) from the unit-square crossing tail
alone. -/
theorem firstPass_11_12_derivedInputsUnitTailOnly
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedInputsUnitTail hUniv (lqgMetricFieldAxiomsUnivFrozen_of_unitTail hUniv)

end HarmonicBalls

namespace HarmonicBalls.S11c

/-- **Derived.** Lemma 11.10 (closed-square form, `SmallMetricDiameterLargeMassSquareStmt`) from the unit-square
crossing tail alone. -/
theorem firstPass_11_10_derivedInputsUnitTailOnly
    (hUniv : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 →
      ∃ δ : ℝ, δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧ ∃ p : ℕ → ℝ≥0∞, ∑' n, 4 ^ n * p n ≠ ⊤ ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ n : ℕ,
            P {ω | ¬ LatticeProb.LQG.HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1
              (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) :
    SmallMetricDiameterLargeMassSquareStmt.{u} :=
  firstPass_11_10_derivedInputsUnitTail hUniv fun γ ξ α₀ Ω _ P hC hcirc =>
    HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_of_unitTail.{u} hUniv Ω P γ ξ α₀ hC hcirc

end HarmonicBalls.S11c

namespace HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed

/-- **Derived.** Lemma 11.13 at the canonical exponent (universe `0`) from the local metric replacement `hN2`, the
continuity of the rooted physical metric at the insertion `hfr` and the unit-square crossing tail `hUniv`. -/
theorem firstPass_11_13_canonical_of_seedInputs_unitTailOnly
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
  firstPass_11_13_canonical_of_seedInputs_unitTail
    (HarmonicBalls.lqgMetricFieldAxiomsUnivFrozen_of_unitTail.{0} hUniv) hN2 hfr hUniv

end HarmonicBalls.FirstPassPhase2Step8WholePlaneFromSeed
