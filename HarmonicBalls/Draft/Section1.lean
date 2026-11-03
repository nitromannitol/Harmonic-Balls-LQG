import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.HarmonicBall
import HarmonicBalls.Defs.Geometry

/-!
# Section 1: statements of Theorems 1.1, 1.2 and Proposition 1.3

Statements of the numbered results of the introduction (lines 150-182 of the corrected draft): existence and uniqueness
of LQG harmonic balls (Theorem 1.1), their novelty and the Jordan boundaries of their complementary components
(Theorem 1.2), and their locality (Proposition 1.3).

## Random setting

Each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ` (line 373: needed for `μ_h` to be locally finite near
the origin), a probability space `(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure
`μ` with `μ ω = μ_h` (`IsLQGMeasureOfField P γ α₀ hcirc μ`), where `h = h^ℂ - α₀ log |·|` (eq:gff, line 380).
"On an event of probability one" is `∀ᵐ ω ∂P`. Theorem 1.2 also quantifies over an LQG metric `D = D_h` of the same
field (`IsLQGMetricOfField P γ ξ α₀ hC D`), for every Weyl exponent `ξ` for which one exists (GM21 construct them for
`ξ = γ / d_γ`, eq:xi, line 440; see `HarmonicBalls/Proposed/LQG.lean`).

## The family of Theorem 1.1

`SatisfiesHarmonicBallConditions μ Λ z` is the list of conditions (a)-(b) of Theorem 1.1 for a family
`Λ : ℝ → Set ℂ` indexed by `t > 0` (values at `t ≤ 0` are irrelevant), and `IsHarmonicBallFamily μ Λ z` adds that
each `Λ t` is a harmonic ball centred at `z` for the enlarged test class (`IsHarmonicBallGen`, lines 136-146). The
phrase "satisfying the conditions of Theorem 1.1" in Proposition 5.4 (line 855), Theorem 5.5 (line 865) and
Proposition 5.6 (line 875) is `SatisfiesHarmonicBallConditions`.

Theorem 1.2 and Proposition 1.3 speak of "the" family `Λ_t(z)` constructed in Theorem 1.1. They are stated for an
arbitrary random family `Λ : Ω → ℝ → Set ℂ` which almost surely is a family of harmonic balls centred at the relevant
point (`0` in Theorem 1.2, `x` in Proposition 1.3) satisfying the conditions of Theorem 1.1. By the almost sure
uniqueness in Theorem 1.1 any such family agrees almost surely, for all `t > 0`, with the family of Theorem 1.1, so
these statements are equivalent, given Theorem 1.1, to the printed ones; no measurability of `Λ` in `ω` is assumed.

## Corrections applied

[C6] (`μ_h(∂Λ_t(z)) = 0`, line 156, printed `∂Λ_t(x)`) in `SatisfiesHarmonicBallConditions`; [C7] (test class: for
some bounded open `O` with `closure Λ ⊆ O`, line 146, printed `Λ ⊂ Ō`) through `IsHarmonicBallGen` of
`Defs/HarmonicBall.lean`. See `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md` and ESCALATIONS E8.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- The conditions (a)-(b) of Theorem 1.1 (theorem:harmonic-balls, lines 152-160) on a family `{Λ_t}_{t > 0}` of
sets, for the measure `μ` (`μ = μ_h` in the paper) and the centre `z`:
* (a) for each `t > 0`, `μ(Λ_t) = t`, `μ(∂Λ_t) = 0` (line 156, with correction [C6]: the printed `∂Λ_t(x)` is
  `∂Λ_t(z)`), and `Λ_t` is equal to the interior of its closure (`IsRegularOpen`);
* (b) the sets `Λ_t` are bounded, connected, contain `z`, increase continuously in `t` in the Hausdorff topology
  (`MonotoneOn` and `HausdorffContinuousOn` on `t > 0`), and `⋂_{t > 0} Λ_t = {z}` (line 157).

The family is indexed by `t > 0`; the values `Λ t` for `t ≤ 0` are not constrained. "Connected" is `IsConnected`
(nonempty and preconnected). -/
structure SatisfiesHarmonicBallConditions (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ) : Prop where
  /-- (a) `μ(Λ_t) = t`. -/
  measure_eq : ∀ t : ℝ, 0 < t → μ (Λ t) = ENNReal.ofReal t
  /-- (a) `μ(∂Λ_t) = 0` (correction [C6]). -/
  measure_frontier : ∀ t : ℝ, 0 < t → μ (frontier (Λ t)) = 0
  /-- (a) `Λ_t` is equal to the interior of its closure. -/
  isRegularOpen : ∀ t : ℝ, 0 < t → IsRegularOpen (Λ t)
  /-- (b) `Λ_t` is bounded. -/
  isBounded : ∀ t : ℝ, 0 < t → Bornology.IsBounded (Λ t)
  /-- (b) `Λ_t` is connected. -/
  isConnected : ∀ t : ℝ, 0 < t → IsConnected (Λ t)
  /-- (b) `Λ_t` contains `z`. -/
  mem : ∀ t : ℝ, 0 < t → z ∈ Λ t
  /-- (b) `Λ_t` increases in `t`. -/
  monotoneOn : MonotoneOn Λ (Ioi 0)
  /-- (b) `Λ_t` is continuous in `t` for the Hausdorff topology. -/
  hausdorffContinuousOn : HausdorffContinuousOn Λ (Ioi 0)
  /-- (b) `⋂_{t > 0} Λ_t = {z}`. -/
  iInter_eq : ⋂ t ∈ Ioi (0 : ℝ), Λ t = {z}

/-- `{Λ_t}_{t > 0}` is a *family of harmonic balls* centred at `z` for `μ` *satisfying the conditions of
Theorem 1.1* (theorem:harmonic-balls, lines 152-160): each `Λ_t`, `t > 0`, is a harmonic ball centred at `z` for the
enlarged class of test functions of lines 136-146 (`IsHarmonicBallGen`, with correction [C7]), and the family
satisfies (a)-(b) (`SatisfiesHarmonicBallConditions`). -/
def IsHarmonicBallFamily (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ) : Prop :=
  (∀ t : ℝ, 0 < t → IsHarmonicBallGen μ (Λ t) z) ∧ SatisfiesHarmonicBallConditions μ Λ z

/-- Theorem 1.1 (theorem:harmonic-balls, line 152). On an event of probability one, for each `z ∈ ℂ`, there exists a
unique family of harmonic balls `{Λ_t(z)}_{t > 0}` for `μ_h` centred at `z` satisfying (a) and (b)
(`IsHarmonicBallFamily`).

The quantifier order of the paper is kept: `∀ᵐ ω ∂P, ∀ z, ∃!`. Uniqueness is uniqueness of the family indexed by
`t > 0`: any two such families agree at every `t > 0` (`EqOn` on `Ioi 0`). Each `Λ_t(z)` is a harmonic ball for the
enlarged test class `f = f₁ + f₂` of lines 143-146 (`IsHarmonicBallGen`). Corrections applied: [C6] (line 156,
`∂Λ_t(z)`), [C7] (line 146, `closure Λ ⊆ O` with `O` bounded open). The paper proves left continuity in `t` only
implicitly (docs/campaign/GRAPH.md, G7); the statement keeps the printed two-sided Hausdorff continuity. -/
def ExistenceUniquenessHarmonicBallsStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ Λ : ℝ → Set ℂ, IsHarmonicBallFamily (μ ω) Λ z ∧
    ∀ Λ' : ℝ → Set ℂ, IsHarmonicBallFamily (μ ω) Λ' z → EqOn Λ' Λ (Ioi 0)

/-- Theorem 1.2 (theorem:harmonic-balls-properties, line 170). On an event of probability 1, for Lebesgue-a.e. `t`,
`Λ_t(0)` is neither a Lipschitz domain nor an LQG-metric ball, and for each `t > 0` the boundaries of the connected
components of `ℂ \ closure Λ_t(0)` are Jordan curves.

`Λ_t(0)` is "the" family of Theorem 1.1 centred at `0`: the statement is made for any random family `Λ` which
almost surely is a family of harmonic balls centred at `0` satisfying the conditions of Theorem 1.1
(`IsHarmonicBallFamily`); by the uniqueness in Theorem 1.1 it is almost surely the family of Theorem 1.1 (see the
module docstring).
* "Lebesgue-a.e. `t`" ranges over `t > 0`, the index set of the family (`∀ᵐ t, 0 < t → ...`), inside the almost
  sure event.
* Lipschitz domain: Definition 11.1 (`IsLipschitzDomain`, line 2712).
* LQG-metric ball: an open ball `𝓑_s(w; D_h) = {v : D_h(w, v) < s}` (`lqgMetricBall`, line 3157) with any centre
  `w ∈ ℂ` and radius `s`, where `D_h` is the γ-LQG metric of the field `h` (`IsLQGMetricOfField`), for every Weyl
  exponent `ξ`. The proof (Proposition 11.11, Lemma 11.15, lines 3091-3234) writes the balls centred at `0`;
  the argument only uses that the centre lies outside `B_{10r}(z)` for small `r`.
* Jordan curve: `IsSimpleLoop` (Definition 10.2, line 2553), the image of an injective continuous map from the circle;
  the components are `connectedComponentsIn (closure Λ_t(0))ᶜ` and the boundary of a component is its `frontier`.

Corrections applied: [C6], [C7] through `IsHarmonicBallFamily`. -/
def HarmonicBallNoveltyStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (ξ : ℝ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P,
    (∀ᵐ t ∂volume, 0 < t →
      ¬ IsLipschitzDomain (Λ ω t) ∧ ∀ (w : ℂ) (s : ℝ), Λ ω t ≠ lqgMetricBall (D ω) w s) ∧
    ∀ t : ℝ, 0 < t → ∀ C ∈ connectedComponentsIn (closure (Λ ω t))ᶜ, IsSimpleLoop (frontier C)

/-- Proposition 1.3 (prop:locally-determined, line 179). For each fixed `t ≥ 0` and `x ∈ ℂ`, the closed LQG harmonic
ball `closure Λ_t(x)` is a local set for `h` (Schramm-Sheffield, *A contour line of the continuum Gaussian free
field*, PTRF 157 (2013), Lemma 3.9): for each deterministic open set `U ⊆ ℂ`, the event
`{closure Λ_t(x) ⊆ U}` is measurable with respect to `σ(h|_U)`.

`Λ_t(x)` is "the" family of Theorem 1.1 centred at `x`: the statement is made for any random family `Λ` which almost
surely is a family of harmonic balls centred at `x` satisfying the conditions of Theorem 1.1
(`IsHarmonicBallFamily`; see the module docstring). Measurability with respect to `σ(h|_U)` (`fieldSigmaAlgebra`) is
up to a `P`-null set: the event is almost surely equal to a `σ(h|_U)`-measurable event (the family itself is only
determined up to a null set).

The statement is for `t ≥ 0`, as printed (line 180). The family of Theorem 1.1 is indexed by `t > 0` (line 153), so the
closed harmonic ball at `t = 0` is read as the point `{x}`, the limit of the family at `t = 0` (Theorem 1.1(b),
line 157: `⋂_{t>0} Λ_t(x) = {x}`; for the closures, eq:contains-origin, line 826); this is a reading, not a correction
(ESCALATIONS E21, operator E20(3)). At `t = 0` the event `{{x} ⊆ U}` is deterministic. Corrections applied: [C6],
[C7] through `IsHarmonicBallFamily`. -/
def HarmonicBallLocalSetStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ (x : ℂ) (Λ : Ω → ℝ → Set ℂ), (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) x) →
  ∀ t : ℝ, 0 ≤ t → ∀ U : Set ℂ, IsOpen U →
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      {ω | (if t = 0 then {x} else closure (Λ ω t)) ⊆ U} =ᵐ[P] E

end HarmonicBalls
