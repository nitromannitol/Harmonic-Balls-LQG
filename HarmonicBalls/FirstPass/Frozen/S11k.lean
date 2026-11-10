import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.Draft.Section11

/-!
# First-pass frozen inputs for Lemma 11.16 (fp-S11k, owner z3)

Three EXTERNAL Props used by `pinchSecondConditionalMass_of_frozen` (`FirstPass/S11k.lean`), the conditional
mass-diameter step of `lemma:massdiam` (corrected paper lines 3511-3523) in the form `lemma:E2` uses (corrected lines
3700-3727). They are general GFF and LQG background (domain Markov, locality and measurability of the LQG mass and of the
internal metric), not statements about this paper's clusters, odometers or harmonic balls. Each was truth-checked TRUE
(ChatGPT, operator note 23:27 UTC, `notes/fp-gaps/CHATGPT-e2-locality-z3-frozen.md` section 4); the operator source-check
of the locators is pending.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- DERIVED INTERFACE (chat 179 Pro audit, CHATGPT-hb-11-12-audit-PRO.md l.173-221). Audit l.202: "It is a normalization-aware
consequence of the GFF Markov decomposition and Cameron–Martin equivalence, not a verbatim proposition."
FIRST-PASS FROZEN. Domain Markov property, conditional positivity form, for a disk `W = ball c r`
(EXTERNAL; Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2: Proposition 2.8 (pp. 48-49: the domain Markov
decomposition of the field on `W` into a zero-boundary GFF plus a harmonic function determined by the outside field) and
Proposition 2.9 (p. 49: Cameron-Martin, equivalence of laws under shifts by `H^1_0(W)`). Truth check TRUE (ChatGPT,
operator note 23:27 UTC, section 4.1); locator pending).

Statement: for an open `O` with `closure O ⊆ W`, every event `A` of the field inside `O` with `P A > 0` (sigma-algebra
`fieldSigmaAlgebra`, with constants) has conditional probability given the field outside `closure W` modulo constants
(`localModConstPairings`) almost surely positive.

Argument (normalization-aware; the full outside field is NOT used, since `W` may meet the normalization circle). Write `ℓ`
for the unit-circle average and `N f = f - ℓ f`. Modulo constants, `h = N Z + H`, with `Z` a zero-boundary GFF on `W`
independent of the outside field modulo constants, and `H` harmonic on `W`, determined by the outside field, `ℓ H = 0`.
Fix `χ ∈ C_c^∞(W)`, `0 ≤ χ ≤ 1`, `χ = 1` near `closure O`, and `a = ℓ χ`. If `a < 1`, let `c = ℓ(χ H)/(1 - a)` and
`φ = χ (H + c)`, so `ℓ φ = c` and `N φ = H` on `O`; if `a = 1`, then `χ = 1` on the unit circle and `φ = χ H` works.
In both cases `φ ∈ H^1_0(W)`. Cameron-Martin gives `Law(Z + φ) ~ Law(Z)`; pushing forward by `z ↦ (N z)|_O` and adding the
deterministic `-α₀ log|·|` shows that all conditional laws of the inner field lie in one measure class, which is also the
class of the unconditional (mixed) law. Hence an inner event of positive probability has positive conditional probability
almost surely. The argument is run on a canonical field space and transferred through the joint law fixed by
`IsWholePlaneGFF`, using countably many pairing coordinates; no regular conditional kernel on the original `Ω` is needed.
Used by: `pinchSecondConditionalMass_of_frozen`, hence `firstPass_11_16_corrected`. -/
def DomainMarkovConditionalPositiveFrozen : Prop :=
  ∀ (α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
  ∀ (W O : Set ℂ), (∃ (c : ℂ) (r : ℝ), 0 < r ∧ W = ball c r) → IsOpen O → closure O ⊆ W →
  ∀ A : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC O] A → 0 < P A →
    ∀ᵐ ω ∂P, 0 < (P[A.indicator (1 : Ω → ℝ) |
      MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance]) ω

/-- DERIVED INTERFACE (chat 179 Pro audit, CHATGPT-hb-11-12-audit-PRO.md l.173-221). Audit l.200: "The right source is HB
Fact 2.1 II, not Fact 2.1 III."
FIRST-PASS FROZEN. Inner measurability of the LQG mass of an open set with compact closure inside `O` (EXTERNAL;
locality and measurable dependence of the LQG measure: Bou-Rabee-Gwynne arXiv:2208.11795v3, Fact 2.1 II (p. 9); truth check
TRUE (ChatGPT, operator note 23:27 UTC); locator pending).

Statement: `μ(U)` is almost surely equal to a random variable measurable for `fieldSigmaAlgebra α₀ hC O`, the sigma-algebra
of the field with its constant (the mass changes by `e^{γc}` under `h ↦ h + c`, so the modulo-constant version is not
claimed). Used by: `pinchSecondConditionalMass_of_frozen`. -/
def LQGMassInnerMeasurableFrozen : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ (O U : Set ℂ), IsOpen O → IsOpen U → Bornology.IsBounded U → closure U ⊆ O →
    ∃ g : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC O] g ∧ ∀ᵐ ω ∂P, μ ω U = g ω

/-- DERIVED INTERFACE (chat 179 Pro audit, CHATGPT-hb-11-12-audit-PRO.md l.173-221). Audit l.201: "The source is HB Fact 2.2
II / GM Axiom II, plus countable reconstruction of the diameter."
FIRST-PASS FROZEN. Inner measurability of the internal diameter `diam^δ(A) = sup_{x,y ∈ A} D(x, y; B_δ(A))` of a compact
set `A` for an LQG metric `D` (`IsLQGMetricOfField`) (EXTERNAL; locality of the internal metric `D(·,·; O)`, which depends
only on `h|_O`, and measurable dependence of the metric on the field: Bou-Rabee-Gwynne arXiv:2208.11795v3, Fact 2.2 II
(p. 10); Gwynne-Miller arXiv:1905.00383v3, Section 1.2, Axiom II (p. 6); truth check TRUE (ChatGPT, operator note 23:27
UTC); locator pending).

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
