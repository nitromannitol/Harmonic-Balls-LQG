import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle

/-!
# Section 3: statements of Lemmas 3.1-3.5 (basic properties of the obstacle problem)

Statements of the numbered results of Section 3.2 (subsec:basic-properties, lines 614-662) of the corrected draft,
for the obstacle problem of Section 3.1 (subsec:obstacle-def, lines 579-602) with measure `μ = μ_h`, the γ-LQG
measure of the field `h = h^ℂ - α₀ log |·|`.

## Random setting

Each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ` (line 373: needed for `μ_h` to be locally finite near
the origin), a probability space `(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure
`μ` with `μ ω = μ_h` (`IsLQGMeasureOfField P γ α₀ hcirc μ`). "On an event of probability 1, for all `t, r, z`" is
`∀ᵐ ω ∂P, ∀ t r z`; Lemma 3.5 ("for each `R > 0` on an event of probability 1") is `∀ R, ∀ᵐ ω ∂P, ...`.

## Conventions

* The obstacle-problem objects are those of `HarmonicBalls/Defs/Obstacle.lean`: `supersolutions` (`S_{B_r;z}(t)`),
  `leastSupersolution` (`v_{B_r;z}(t)`), `cluster` (`Λ_{B_r;z}(t)`), `odometer` (`u_{B_r;z}(t)`). They are defined
  (line 581) for `t, r > 0` and `z ∈ B_r`, which are hypotheses of every statement.
* "Finite" for the least supersolution (an infimum, possibly `-∞` a priori, see `leastSupersolution`) is the bounded
  below property of the set of values of supersolutions at every point of the closed ball.
* Differential identities are distributional (line 325): `HasLaplacian w μpos μneg U` is `Δw = μpos - μneg` in `U`.
* "Connected" is `IsConnected` (nonempty and preconnected; the cluster contains the pole).

## Corrections applied

[C3] (pole `z` of the odometer and of the cluster, lines 593, 597) through `odometer` and `cluster` of `Defs/Obstacle.lean`;
[C4] (`μ` → `μ_h` in Lemma 3.4, line 650). See `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`.
-/

namespace HarmonicBalls

open MeasureTheory Metric

/-- Lemma 3.1 (lemma:basic-properties, line 621). On an event of probability 1, for all `t, r > 0` and `z ∈ B_r`,
the least supersolution `v_{B_r;z}(t)` (eq:least-super-solution, line 588) is finite, continuous, and an element of
`S_{B_r;z}(t)` (eq:super-solutions, line 583), for `μ = μ_h`.

"Finite" is the bounded below property of `{w(x) : w ∈ S_{B_r;z}(t)}` at every `x` in the closed ball (an infimum
over a nonempty set, `0 ∈ S_{B_r;z}(t)`, is never `+∞`); it is automatic off the pole (`bddBelow_supersolutions`),
so its content is finiteness at the pole `z`, where the obstacle is `-∞`. "Continuous" is continuity on the closed
ball, the domain of `C(\overline{B_r})`. Corrections applied: none (C3 enters only through the odometer). -/
def LeastSupersolutionMemStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    (∀ x ∈ closedBall (0 : ℂ) r, BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions (μ ω) r z t)) ∧
    ContinuousOn (leastSupersolution (μ ω) r z t) (closedBall 0 r) ∧
    leastSupersolution (μ ω) r z t ∈ supersolutions (μ ω) r z t

/-- Lemma 3.2 (lemma:non-coincidence-open-harmonic, line 627). On an event of probability 1, for all `t, r > 0` and
`z ∈ B_r`, the cluster `Λ = Λ_{B_r;z}(t)` (eq:non-co-set, line 593) is open and connected, and there is a Radon
measure `ν`, absolutely continuous with respect to `μ_h` on `B_r` with `0 ≤ ν ≤ μ_h` on `B_r`, such that
`Δ v_{B_r;z}(t) = μ_h|_Λ + ν|_{∂Λ}` on `B_r`; in particular (same `ν`)
`Δ u_{B_r;z}(t) = -t δ_z + μ_h|_Λ + ν|_{∂Λ}` on `B_r` for the odometer (eq:limit-odometer, line 597).

"Radon" is `IsLocallyFiniteMeasure ν`; "on `B_r`" for the comparison with `μ_h` is restriction to `B_r`. The two
identities are distributional on `B_r` (`HasLaplacian`, line 325): the first with negative part `0`, the second with
negative part `t δ_z`. The boundary `∂Λ` is `frontier Λ`. Corrections applied: [C3] (the odometer and the cluster
have the pole `z`, lines 593, 597; the printed `-t δ_z` at line 635 requires it). -/
def ClusterOpenLaplacianStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t r : ℝ, 0 < t → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    IsOpen (cluster (μ ω) r z t) ∧ IsConnected (cluster (μ ω) r z t) ∧
    ∃ ν : Measure ℂ, IsLocallyFiniteMeasure ν ∧
      ν.restrict (ball 0 r) ≪ (μ ω).restrict (ball 0 r) ∧
      ν.restrict (ball 0 r) ≤ (μ ω).restrict (ball 0 r) ∧
      HasLaplacian (leastSupersolution (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t))) 0
        (ball 0 r) ∧
      HasLaplacian (odometer (μ ω) r z t)
        ((μ ω).restrict (cluster (μ ω) r z t) + ν.restrict (frontier (cluster (μ ω) r z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 r)

/-- Lemma 3.3 (lemma:monotonicity, line 644). On an event of probability 1, for all `t₁ ≤ t₂`, `r > 0` and
`z ∈ B_r`, `Λ_{B_r;z}(t₁) ⊆ Λ_{B_r;z}(t₂)`.

The printed clusters `Λ^{B_r}_{t_i}` (line 645) omit the pole `z`, which is quantified; they are read as
`Λ^{B_r;z}_{t_i}` (by the convention of line 601 the omission of `z` would mean `z = 0`, making the quantifier over
`z` idle). The clusters are defined for
`t > 0` (line 581), hence `0 < t₁`. Corrections applied: none. -/
def ClusterMonotoneStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t₁ t₂ r : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < r → ∀ z ∈ ball (0 : ℂ) r,
    cluster (μ ω) r z t₁ ⊆ cluster (μ ω) r z t₂

/-- Lemma 3.4 (lemma:conservation-of-mass, line 649). On an event of probability 1, for all `r, t > 0` and
`z ∈ B_r`: `μ_h(Λ_{B_r;z}(t)) ≤ t` and the odometer `u_{B_r;z}(t)` vanishes on `∂B_r`; moreover, if
`closure Λ_{B_r;z}(t) ⊂ B_r` and `μ_h(∂Λ_{B_r;z}(t)) = 0`, then `μ_h(Λ_{B_r;z}(t)) = t`.

Corrections applied: [C4] (the printed hypothesis `μ(∂Λ) = 0`, line 650, reads `μ_h(∂Λ) = 0`); [C3] through
`odometer` (pole `z`). -/
def ClusterConservationOfMassStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ r t : ℝ, 0 < r → 0 < t → ∀ z ∈ ball (0 : ℂ) r,
    μ ω (cluster (μ ω) r z t) ≤ ENNReal.ofReal t ∧
    (∀ x ∈ sphere (0 : ℂ) r, odometer (μ ω) r z t x = 0) ∧
    (closure (cluster (μ ω) r z t) ⊆ ball 0 r → μ ω (frontier (cluster (μ ω) r z t)) = 0 →
      μ ω (cluster (μ ω) r z t) = ENNReal.ofReal t)

/-- Lemma 3.5 (lemma:cluster-compatibility, line 657). For each `R > 0`, on an event of probability 1: for all
`t > 0`, `s₁ ≤ R` and `z ∈ B_{s₁}`, if `closure Λ_{B_{s₂};z}(t) ⊂ B_{s₁}` for some `s₂ ∈ [s₁, R]`, then
`Λ_{B_s;z}(t) = Λ_{B_{s₂};z}(t)` for all `s ∈ [s₁, R]`.

The printed statement leaves `t` unbound (line 659); it is quantified inside the event of probability 1, as for
Lemmas 3.1-3.4 (Lemma A.6, from which it follows, is deterministic given the volume growth condition on `B_R`).
`z ∈ B_{s₁}` forces `s₁ > 0`. Corrections applied: [C3] through `cluster` (pole `z`). -/
def ClusterCompatibilityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ R : ℝ, 0 < R →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ R → ∀ z ∈ ball (0 : ℂ) s₁,
    ∀ s₂ ∈ Set.Icc s₁ R, closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
      ∀ s ∈ Set.Icc s₁ R, cluster (μ ω) s z t = cluster (μ ω) s₂ z t

end HarmonicBalls
