import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Draft.Section1

/-!
# Section 10: statements of Lemmas 10.1, 10.5 and Propositions 10.6, 10.7

Statements of the numbered results of Section 10 (sec:boundary-curves, lines 2476-2697 of the corrected draft): the
clusters cross annuli boundedly many times, and the boundaries of the complementary components of the clusters and
of the harmonic balls are simple loops (Jordan curves). Definitions 10.2-10.4 are in `HarmonicBalls/Defs/Geometry.lean`.

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`).

## Objects

* `Λ_t(z)` (`\cluster{}{t}(z)`, lines 2479-2624) is the cluster `Λ_{B_1;z}(t)` of the unit ball (eq:non-co-set,
  line 592; convention of line 601): `cluster (μ ω) 1 z t` of `Defs/Obstacle.lean`.
* `Λ̂_t(z)` (`\regcluster{}{t}(z)`, Proposition 10.7, line 2685) is the harmonic ball family of Theorem 5.5
  (theorem:full-theorem-minus-uniqueness, line 863), which by the uniqueness of Theorem 1.1 is the family of
  Theorem 1.1. As in `Draft/Section1.lean`, the statement is made for any random family `Λ` which is almost surely,
  for every `z`, a harmonic ball family at `z` (`IsHarmonicBallFamily`, Theorem 1.1 with correction [C7]).
* `A ⋐ B` (line 329) is `closure A ⊆ B`; "crosses" (line 2582) is `CrossesAnnulus`, the crossing components are
  `crossingComponents`, the connected components of a set are `connectedComponentsIn`, "simple loop" is
  `IsSimpleLoop` (Definition 10.2). "Simply connected" (Lemma 10.5, line 2586) is meant in the Riemann-sphere sense
  of the paper, "connected with connected complement" (proof of Proposition 10.6, lines 2646 and 2661): for the
  component `U` of `(closure Λ_t(z))ᶜ` (connected, open) it is `IsConnected Uᶜ`, not Mathlib's planar
  `IsSimplyConnected` (which fails for the unbounded component, whose fundamental group is `ℤ`).

## Corrections and readings

* Proposition 10.6 (line 2623) is false as printed (see `ComplementComponentBoundarySimpleLoopStmt`); it is stated
  for the components of `ℂ \ closure Λ_t(z)`, as in its proof (line 2628) and in Proposition 10.7 (proposed
  correction, reported by c4).
* Lemma 10.5 (line 2585) carries no probability qualifier; the clusters have the properties used in its proof
  (Lemma 3.2, line 627) on an event of probability one, and the statement is made on such an event (`∀ᵐ ω ∂P`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Lemma 10.1 (lemma:cannot-cross, line 2496). There is a deterministic `α = α(γ) ∈ (0,1)` (the constant of
Proposition 6.2, prop:harnack-type-stronger-property, line 1078) such that, with `K := ⌈1/α⌉`, almost surely, for
each small enough `ε > 0` and each `w ∈ B_1 \ B_{20 √ε}` there is a radius `ρ ∈ [ε, ε^{1/2}]` (depending on `w`)
such that for every `t > 0` and `z ∈ ℂ` with `Λ_t(z) ⋐ B_1`, at most `K` connected components of
`Λ_t(z) ∩ B_{2ρ}(w)` cross the annulus `𝔸_{ρ/3,2ρ}(w)` (their closures meet both `∂B_{ρ/3}(w)` and `∂B_{2ρ}(w)`).

`α` depends on `γ` only, as printed, so it is chosen before `α₀`. The link with Proposition 6.2 is recorded only in
this docstring: the content of the lemma is the deterministic bound `⌈1/α⌉`. For `z ∉ B_1` the cluster is empty
(`cluster` is a subset of `B_1` containing no pole) and the conclusion is trivial; `z ∈ ℂ` is kept as printed. -/
def ClusterBoundedCrossingsStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1, ∀ α₀ : ℝ, α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
    ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ z : ℂ, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊

/-- Lemma 10.5 (lemma:crossing-connected, line 2585). Let `A = 𝔸_{s₁,s₂}(w) ⋐ B_1` be an annulus (`0 < s₁ < s₂`,
eq:annulus, line 333), `t > 0` and `z ∈ B_1` with `Λ_t(z) ⋐ B_1`, and let `U` be a simply connected component of
`(closure Λ_t(z))ᶜ` with `Γ = ∂U ⋐ B_1`. Then every connected component of `Uᶜ ∩ A` which crosses `A` contains a
connected component of `Λ_t(z) ∩ A` which crosses `A`.

"Simply connected" is the Riemann-sphere sense of the paper (line 2661: "`U` is connected with connected complement,
so is simply connected"; Step 1 of Proposition 10.6, line 2646: "As `U^c` is connected"): `IsConnected Uᶜ`, the
complement taken in `ℂ` (for the unbounded component this is simple connectivity of `U ∪ {∞}` in the sphere). It is
not Mathlib's planar `IsSimplyConnected U`, which excludes the unbounded component of `(closure Λ_t(z))ᶜ` (fundamental
group `ℤ`), to which Step 1 of Proposition 10.6 applies the lemma (operator 2026-11-03 04:45, fix (1); freeze review
MISMATCH). Proposition 10.6 applies the lemma to every component: on the event of Lemma 3.2 (`ClusterOpenLaplacianStmt`)
the cluster is connected, so `K = closure Λ_t(z)` is connected and nonempty, and for each component `U` of `Kᶜ` the
complement `Uᶜ = K ∪ ⋃ V` (`V` the other components, each with `closure V ⊆ V ∪ K` meeting `K`) is connected.

The printed lemma carries no probability qualifier; it is stated on an event of probability one, on which the
clusters have the properties of Lemma 3.2 used in the proof. -/
def CrossingComponentContainsClusterCrossingStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ (w : ℂ) (s₁ s₂ : ℝ), 0 < s₁ → s₁ < s₂ → closure (annulus w s₁ s₂) ⊆ ball 0 1 →
    ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ, IsConnected Uᶜ →
    closure (frontier U) ⊆ ball 0 1 →
    ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w s₁ s₂) w s₁ s₂,
      ∃ C' ∈ crossingComponents (cluster (μ ω) 1 z t ∩ annulus w s₁ s₂) w s₁ s₂, C' ⊆ C

/-- Proposition 10.6 (prop:boundary-simple-loop, line 2622), corrected. Almost surely, for all `t > 0` and `z ∈ B_1`
with `Λ_t(z) ⋐ B_1`, each connected component of `ℂ \ closure Λ_t(z)` has a boundary which is a simple loop.

**The printed statement is false.** It reads "each of the connected components of `B_1 \ closure Λ_t(z)`". Since
`K := closure Λ_t(z)` is a non-empty compact subset of `B_1` (it contains `z`), the component `C₀` of `B_1 \ K`
containing `B_1 \ closedBall 0 (1 - η)` (`η > 0` small) has a boundary containing the whole circle `∂B_1` and a point
of `K` (otherwise `C₀` would be closed in `B_1`, hence equal to `B_1`). So `∂C₀ ⊆ ∂B_1 ∪ K` meets both disjoint
closed sets and is disconnected, while a simple loop is connected. The proof (line 2628: "let `U` be a component of
`(closure Λ_t(z))ᶜ`") and Proposition 10.7 (line 2685) use the complement in `ℂ`; this is the statement below. It is
equivalent to the printed one with "boundary" read relative to `B_1` (the components of `B_1 \ K` are those of
`ℂ \ K` intersected with `B_1`, and their boundaries in `B_1` are those in `ℂ` of the components of `ℂ \ K`). -/
def ComplementComponentBoundarySimpleLoopStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    ∀ C ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ, IsSimpleLoop (frontier C)

/-- Proposition 10.7 (prop:boundary-simple-loop-full-cluster, line 2684). Almost surely, for all `t > 0` and
`z ∈ ℂ`, each connected component of `ℂ \ closure Λ̂_t(z)` has a boundary which is a simple loop.

`Λ̂_t(z)` is the harmonic ball family of Theorem 5.5 / Theorem 1.1 centred at `z`: the statement is made for any
random family `Λ ω z t` which is almost surely, for every `z`, a harmonic ball family at `z`
(`IsHarmonicBallFamily`); given the uniqueness of Theorem 1.1 this is the printed statement. -/
def HarmonicBallComplementBoundaryJordanStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsHarmonicBallFamily (μ ω) (Λ ω z) z) →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ℂ,
    ∀ C ∈ connectedComponentsIn (closure (Λ ω z t))ᶜ, IsSimpleLoop (frontier C)

end HarmonicBalls
