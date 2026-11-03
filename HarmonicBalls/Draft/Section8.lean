import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.Annuli

/-!
# Section 8: statements of Proposition 8.1 and Lemmas 8.2, 8.3

Statements of the numbered results of Section 8 (sec:boundary-measure-zero, lines 2119-2275 of the corrected draft):
the boundary of a cluster compactly contained in the unit ball has `μ_h`-measure zero (Proposition 8.1), from the
Lebesgue density theorem and the existence, around `μ_h`-typical points (Lemma 8.2) and around the origin for a
field with a logarithmic singularity there (Lemma 8.3), of many dyadic scales at which the annulus is very good and
the annulus-ball comparison holds.

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`), where `h = h^ℂ - α₀ log |·|`. Deterministic constants are chosen before the
probability space.

## Good and very good annuli (Section 6.2, lines 1105-1161)

The good annulus event `IsGoodAnnulus`, the size `annulusBallMassSize` (`M_ρ`), `annulusGreenPotentialSup` (`SG`), the
very good annulus event `IsVeryGoodAnnulus`, the annulus-ball comparison `AnnulusBallComparison` (`G_n(z; m)`) and the
count `veryGoodComparableScaleCount` of eq:mu_h-doubling are deterministic predicates of the measure `μ`, shared with
Sections 6 and 11, in `HarmonicBalls/Defs/Annuli.lean` (with the reading of the slip at line 1120 and Issues D10, G21).

## Corrections and readings

* `β⁻` in `M_ρ` (eq:alternate-size, line 1129) is "the" lower exponent of Lemma 2.4, which allows any
  `β⁻ > (2+γ)²/2`. The statements hold for each such `β⁻` (Issue D10).
* Parameter interface of Lemmas 8.2 and 8.3 (Issue G28). As printed, "there exist `m` and parameters" is one
  existential block. Proposition 8.1 needs one tuple valid for Lemma 6.11 as well, with `C₃` fixed before `b`
  (Lemma 6.11 holds for every `C₃` with `b = b(γ, C₃)`, Issue G18) and `N₀` arbitrarily large (caption at
  lines 1588-1590). The statements are therefore made in the form the proofs give:
  `∃ C₃, ∀ ζ b, ∃ a C₁^± C₂^± N₁, ∀ N₀ ≥ N₁, ∃ m`. This is stronger than the printed form.
* Proposition 8.1 (line 2124): `t` is unbound (S 2124). The proof (lines 2230-2274) uses null sets that do not depend
  on `(t, z)`, so the statement is made on one event for all `t > 0` and `z` simultaneously.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-! ## Statements -/

/-- Proposition 8.1 (prop:boundary-measure-zero, line 2122). On an event of probability one,
`μ_h(∂Λ_t^z) = 0` for all `z ∈ B_1` with `Λ_t^z ⋐ B_1`.

Readings: `Λ_t^z` is `cluster (μ ω) 1 z t` (eq:non-co-set, line 592), `⋐` is `closure _ ⊆ _`, and `∂` is
`frontier`. The unbound `t` (S 2124) is read as "for all `t > 0`", on the same event as `z` (the null sets of the
proof, eq:density-0 and Lemma 8.2, do not depend on `(t, z)`). -/
def BoundaryMeasureZeroOfCompactClusterStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    μ ω (frontier (cluster (μ ω) 1 z t)) = 0

/-- Lemma 8.2 (lemma:mu_h-doubling-and-harnack, line 2151). Let `ζ > 0` and `b ∈ (0,1)`. There exist `m > 0` and
parameters `N₀, a, C₁^±, C₂^±, C₃` of the very good event `Ē_ρ(z)` such that almost surely, for `μ_h`-a.e.
`z ∈ B_1`, for each large enough `N ∈ ℕ` (depending on `z`),
`#{n ∈ [N+1, 2N] ∩ ℤ : Ē_n(z) and G_n(z) occur} ≥ (1 - ζ) N` (eq:mu_h-doubling).

Readings:
* parameter order (Issue G28, module docstring): `∃ C₃ > 0, ∀ ζ > 0, ∀ b ∈ (0,1), ∃ a ∈ (0,1), C₁^±, C₂^± > 0,
  N₁ ≥ 1, ∀ N₀ ≥ N₁, ∃ m > 0`. `C₃` is the universal constant of Lemma 6.7 (lemma:very-good-annuli-hit, line 1307),
  which the proof reaches through Lemma 8.3 at the singularity `γ`; it is allowed to depend on `γ`, `α₀`, `β⁻`;
* `β⁻ > (2+γ)²/2` is the exponent of `M_ρ` (eq:alternate-size, line 1129). The annuli are centred at `μ_h`-typical
  points `z ≠ 0` at scales `2^{-n} → 0`, so the correction [C1] near the origin does not enter;
* "for `μ_h`-a.e. `z ∈ B_1`" is `∀ᵐ z ∂ (μ ω).restrict B_1`, inside `∀ᵐ ω ∂P`. -/
def TypicalPointManyGoodScalesStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball (0 : ℂ) 1), ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N

/-- Lemma 8.3 (lemma:doubling-alpha, line 2160). Let `ζ > 0` and `b ∈ (0,1)`. There exist `m > 0` and parameters
`N₀, a, C₁^±, C₂^±, C₃` of the very good event `Ē_ρ(0)` such that almost surely, for each large enough `N ∈ ℕ`,
`#{n ∈ [N+1, 2N] ∩ ℤ : Ē_n(0) and G_n(0) occur} ≥ (1 - ζ) N` (eq:mu_h-doubling at `z = 0`).

Readings:
* the field is `h = h^ℂ - α₀ log |·|` for every `α₀ < Q`: Lemma 8.2 applies this lemma with `α₀ = γ` (line 2220,
  Issue G30), so the exponent of the singularity at the centre is a quantified variable, not the global `α₀`;
* parameter order as in `TypicalPointManyGoodScalesStmt` (Issue G28); the constants may depend on `γ`, `α₀`, `β⁻`
  (Lemma 6.7 prints no `α₀`-dependence, Issue G30);
* `β⁻ > (2+γ)²/2`: the annuli `𝔸_{ρ/4,2ρ}(0)` are centred at the singularity, and the law of every ratio in `Ē_ρ(0)`
  and `G_n(0)` does not depend on the scale (eq:h-coordinate-change, line 386), so [C1] does not enter. -/
def OriginManyGoodScalesStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) βminus 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N

end HarmonicBalls
