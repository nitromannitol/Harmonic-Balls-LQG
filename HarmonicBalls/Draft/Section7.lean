import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle

/-!
# Section 7: statements of Propositions 7.1 and 7.2

Statements of the numbered results of Section 7 (sec:upper-bound, lines 1950-2118 of the corrected draft): the
clusters do not immediately exit the unit ball (Proposition 7.1), and they are Hölder continuous from the right in
the mass parameter `t` (Proposition 7.2).

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`). Deterministic constants are chosen before the probability space.

## Objects

* `Λ_t^z` (`\cluster{z}{t}`) is the cluster `Λ_{B_1;z}(t)` of the unit ball (eq:non-co-set, line 592; convention of
  line 601): `cluster (μ ω) 1 z t` of `Defs/Obstacle.lean`. The mass parameter is `t > 0` throughout the paper; the
  statements are made for `t > 0` only.
* `A ⋐ B` (line 329) is `closure A ⊆ B`. The Minkowski sum `Λ + B_δ` is `Λ + ball 0 δ` (pointwise addition), the open
  `δ`-neighbourhood of `Λ`.
* "With polynomially high probability as `T → 0`" (line 336) is `PolyHighProb` of `Defs/Notation.lean`.

## Corrections and readings

* Proposition 7.2 (line 2025) prints `Λ_t^z + B_δ(z)`; the proof (eq:boundary-inside, line 2046; eq:zero-on-shell,
  line 2078) works with the neighbourhood `Λ_t^z + B_δ` (slip S 2025, `docs/campaign/GRAPH.md`).
* Proposition 7.2: `β⁻` "is from Lemma 2.4" (line 2026). Lemma 2.4 is in force with correction [C1], so `β⁻` ranges
  over its corrected range `β⁻ > max((2+γ)²/2, γ(Q-α₀))`. The proof applies Lemma 2.4 at grid points of all of `B_1`,
  near the origin included (Issue G27: `0` may lie on `∂Λ_t^z`).
* The repairs of the proofs (Issues G26, G27 for the covers near the origin; G29: the mass identity at line 2058 needs
  Proposition 8.1; G1) do not change the statements.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

/-- Proposition 7.1 (prop:upper-bound-polynomially-high-prob, line 1956). For each `r ∈ (0,1)`, on an event which
occurs with polynomially high probability as `T → 0`,
`closure (Λ_t^z) ⊆ B_{r/2}(z)` for all `t ≤ T` and all `z ∈ B_{1/2}`.

Reading: the event is `{∀ t ∈ (0, T], ∀ z ∈ B_{1/2}, closure Λ_t^z ⊆ B_{r/2}(z)}` (the mass parameter is positive,
see the module docstring); the polynomial rate (exponent and constant of `PolyHighProb`) may depend on `r`. The
statement holds for all `z ∈ B_{1/2}` and all `t ≤ T` simultaneously on one event, as printed (line 1964). The proof
(lines 1968-2006) needs the cover repair G26 near the origin, which keeps the statement. -/
def ClusterUpperBoundPolyHighProbStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ r ∈ Ioo (0 : ℝ) 1,
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)})

/-- Proposition 7.2 (prop:continuity-of-clusters, line 2021). On an event of probability one: for each `t > 0` and
`z ∈ B_1` with `Λ_t^z ⋐ B_1`, for all `ε > 0` sufficiently small (depending on `t`),
`Λ_{t+ε}^z ⋐ Λ_t^z + B_δ` with `δ = C ε^{1/(4β⁻)}`, where `β⁻` is an exponent of Lemma 2.4 and `C > 0` is a
deterministic constant.

Readings (see the module docstring for the Minkowski sum and the range of `β⁻`):
* quantifier order as printed: `∀ β⁻`, `∃ C` (deterministic), then almost surely `∀ t, ∀ z`, then "for all small
  `ε`" (`∀ᶠ ε in 𝓝[>] 0`; the threshold depends on `ω`, `t` and `z`);
* `C = C(β⁻)` is printed; the proof gives `C = 4 √2 α^{-1/(4β⁻)}` with `α = α(γ)` the constant of Proposition 6.1,
  which may also depend on `α₀` (Issue G19(iii)). So `C` is chosen after `γ`, `α₀` and `β⁻`;
* only right-continuity is claimed (Issue G7). -/
def ClusterTimeContinuityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ βminus : ℝ, max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
  ∃ C : ℝ, 0 < C ∧
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      closure (cluster (μ ω) 1 z (t + ε)) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) (C * ε ^ (1 / (4 * βminus)))

end HarmonicBalls
