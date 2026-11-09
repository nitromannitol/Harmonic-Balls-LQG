import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.Draft.Section11

/-!
# First-pass frozen inputs for Lemma 11.16 (fp-S11k, owner z3)

Three EXTERNAL Props used by `pinchSecondConditionalMass_of_frozen` (`FirstPass/S11k.lean`), the conditional
mass-diameter step of `lemma:massdiam` (corrected paper lines 3511-3523) in the form `lemma:E2` uses (corrected lines
3700-3727). They are general GFF and LQG background (domain Markov, locality and measurability of the LQG mass and of the
internal metric), not statements about this paper's clusters, odometers or harmonic balls. None is operator-checked yet.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- FIRST-PASS FROZEN. Domain Markov property, conditional positivity form, for a disk `W = ball c r`
(EXTERNAL; Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.8 (pp. 48-49: given the field outside
`W`, the field inside is an independent zero-boundary GFF plus a harmonic function) and Proposition 2.9 (p. 49:
Cameron-Martin, equivalence of the laws under shifts by `H^1_0(W)`); locator pending).

Statement: for an open `O` with `closure O ⊆ W`, every event `A` of the field inside `O` with `P A > 0` (sigma-algebra
`fieldSigmaAlgebra`, with constants) has conditional probability given the field outside `closure W` modulo constants
(`localModConstPairings`) almost surely positive. The argument behind it (for the operator's check): conditionally on the
full outside field the inside field restricted to `O` is a shift of the zero-boundary GFF law by `χ H_y`, with
`χ ∈ C_c^∞(W)`, `χ = 1` near `closure O`, and `χ H_y ∈ H^1_0(W)`, so the conditional laws are mutually absolutely continuous;
then the tower property passes from the full outside sigma-algebra to the modulo-constant one.
Used by: `pinchSecondConditionalMass_of_frozen`, hence `firstPass_11_16_corrected`. -/
def DomainMarkovConditionalPositiveFrozen : Prop :=
  ∀ (α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
  ∀ (W O : Set ℂ), (∃ (c : ℂ) (r : ℝ), 0 < r ∧ W = ball c r) → IsOpen O → closure O ⊆ W →
  ∀ A : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC O] A → 0 < P A →
    ∀ᵐ ω ∂P, 0 < (P[A.indicator (1 : Ω → ℝ) |
      MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance]) ω

/-- FIRST-PASS FROZEN. Inner measurability of the LQG mass of an open set with compact closure inside `O` (EXTERNAL;
locality and measurable dependence of the LQG measure, Bou-Rabee-Gwynne arXiv:2208.11795, Fact 2.1 III (p. 9), and
Duplantier-Sheffield arXiv:0808.1560v2, Section 3, where the approximations of `μ(U)` use circle averages of radius below
`dist(U, ∂O)` only; locator pending).

Statement: `μ(U)` is almost surely equal to a random variable measurable for `fieldSigmaAlgebra α₀ hC O`, the sigma-algebra
of the field with its constant (the mass changes by `e^{γc}` under `h ↦ h + c`, so the modulo-constant version is not
claimed). Used by: `pinchSecondConditionalMass_of_frozen`. -/
def LQGMassInnerMeasurableFrozen : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ (O U : Set ℂ), IsOpen O → IsOpen U → Bornology.IsBounded U → closure U ⊆ O →
    ∃ g : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC O] g ∧ ∀ᵐ ω ∂P, μ ω U = g ω

/-- FIRST-PASS FROZEN. Inner measurability of the internal diameter `diam^δ(A) = sup_{x,y ∈ A} D(x, y; B_δ(A))` of a compact
set `A` for an LQG metric `D` (`IsLQGMetricOfField`) (EXTERNAL; locality of the internal metric `D(·,·; O)`, which depends
only on `h|_O`, and measurable dependence of the metric on the field, Bou-Rabee-Gwynne arXiv:2208.11795, Fact 2.2 I (p. 9,
lines 432-457); Gwynne-Miller 2021, Section 1.2 (p. 6); locator pending).

Statement: with `O = thickening δ A`, the internal diameter is almost surely equal to a random variable measurable for
`fieldSigmaAlgebra α₀ hC O`. Only this a.s. form is claimed (the infimum over paths is not measurable as a function of the
whole distribution, `LQGInternalMetricWeylAeMeasurableFrozen`). Used by: `pinchSecondConditionalMass_of_frozen`. -/
def LQGInternalDiamInnerMeasurableFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ (δ : ℝ) (A : Set ℂ), 0 < δ → IsCompact A →
    ∃ g : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (thickening δ A)] g ∧
      ∀ᵐ ω ∂P, internalDiam (D ω) δ A = g ω

end HarmonicBalls
