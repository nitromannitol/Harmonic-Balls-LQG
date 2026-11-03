import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LBM

/-!
# Section 2: statements of Proposition 2.3, Lemma 2.4 and Propositions 2.5-2.6

Statements of the numbered results of Sections 2.3-2.4 (subsec:green, subsec:lqg-appendix, lines 466-562) of the
corrected draft paper/lqg_harmonic_ball-corrected.tex, and of two unnumbered consequences used throughout the paper
(inputs I1 and I2 of docs/campaign/GRAPH.md). Facts 2.1-2.2 are literature inputs (HarmonicBalls/Proposed/LQG.lean)
and are not drafted here.

## Random setting

Each random statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ` (line 373: needed for `μ_h` to be locally finite
near the origin), a probability space `(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random
measure `μ` with `μ ω = μ_h` (`IsLQGMeasureOfField P γ α₀ hcirc μ`), where `h = h^ℂ - α₀ log |·|` (eq:gff, line 380).
Liouville Brownian motion (LBM) is the time change of planar (or reflected) Brownian motion by the LQG clock
(`IsLQGClock`, HarmonicBalls/Defs/LBM.lean), and the clocks are parameters `F ω x` (for the field `h(ω)` and the
starting point `x`) with the defining property `IsLQGClock` holding almost surely.

## Conventions

* `greenFunction O x y` takes the junk value `0` on the diagonal and off `O × O` (HarmonicBalls/Defs/Green.lean). The
  zero boundary values of Proposition 2.3 are therefore stated together with the limit `G(x, y) → 0` as `y → ∂B_R`
  within `B_R`, which is their content for the paper's `G_{B_R} : closure B_R × closure B_R → ℝ ∪ {∞}`; positivity is
  stated off the pole.
* Differential identities are distributional (line 326): `HasLaplacian w μpos μneg U` is `Δw = μpos - μneg` in `U`.
* "With polynomially high probability as `ε → 0`" is `PolyHighProb` (line 336); the events are the sets of `ω` on
  which the displayed bounds hold for all `z` in the stated set.
* Hölder continuity is Mathlib's `HolderOnWith C r` with exponent `r > 0`.
* "Almost surely" is placed as early as the paper's proofs allow, i.e. one event for all sets `O` and all functions
  `f` (Proposition 2.5) or all radii and exponents (I2).

## Corrections applied

[C1] (Lemma 2.4, lines 497-506: exponent ranges `β⁺ < min {(2-γ)²/2, γ(Q-α₀)}` and `β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`,
both displays; the printed range fails at `z = 0` for `α₀ ∉ [-2, 2]`, ESCALATIONS.md E1) and [C5] (Proposition 2.6,
line 547: the heat kernel is a density with respect to `μ_h`, through `IsLBMHeatKernel`). The volume-growth
statement I2 is eq:volume-growth (line 3527) with [C2] (upper exponent `β⁺`) and the exponent ranges of [C1].
See `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`.

## Normalization remark (not a correction)

Line 468 calls `G_O` "the Green's function for standard Brownian motion killed upon exiting `O`", while
Proposition 2.3 (line 482) normalizes `ΔG_O(x,·) = -δ_x`, i.e. `G_O(x,y) = -(2π)⁻¹ log |x-y| + harmonic`. Standard
Brownian motion has generator `Δ/2`, so its occupation density (Green function) is `2 G_O`; for instance
`E_x[τ_O] = 2 ∫_O G_O(x,y) dy`. The statements below are insensitive to this factor (finiteness and Hölder
continuity); they follow the normalization of Proposition 2.3, as HarmonicBalls/Defs/Green.lean does.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess Metric Filter Topology Set
open scoped ENNReal NNReal

/-! ### Proposition 2.3: the Green function of a ball -/

open scoped ContDiff in
/-- Proposition 2.3 (prop:green-properties, line 480). For `R > 0` and every `x ∈ B_R = B_R(0)`, the Green function
`G_{B_R}(x,·)` of the ball

* is a fundamental solution: `ΔG_{B_R}(x,·) = -δ_x` on `B_R`, in the distributional sense (line 326);
* is positive on `B_R` (off the pole `x`, where the paper's value is `+∞` and `greenFunction` has the junk value `0`);
* has zero boundary values on `∂B_R`: it vanishes there and `G_{B_R}(x,y) → 0` as `y → ∂B_R` within `B_R`;
* is infinitely differentiable (`C^∞`) away from the pole, on `B_R \ {x}`. -/
def GreenFunctionBallStmt : Prop :=
  ∀ R : ℝ, 0 < R → ∀ x ∈ ball (0 : ℂ) R,
    HasLaplacian (greenFunction (ball 0 R) x) 0 (Measure.dirac x) (ball 0 R) ∧
    (∀ y ∈ ball (0 : ℂ) R, y ≠ x → 0 < greenFunction (ball 0 R) x y) ∧
    (∀ y ∈ sphere (0 : ℂ) R, greenFunction (ball 0 R) x y = 0 ∧
      Tendsto (greenFunction (ball 0 R) x) (𝓝[ball 0 R] y) (𝓝 0)) ∧
    ContDiffOn ℝ ∞ (greenFunction (ball 0 R) x) (ball 0 R \ {x})

/-! ### Lemma 2.4: LQG mass of balls and annuli -/

/-- Lemma 2.4 (lemma:volume-growth, line 497), with correction [C1]. For each `β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})` and
each `β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`:

* (eq:ball-volume) with polynomially high probability as `ε → 0`, `ε^{β⁻} ≤ μ_h(B_ε(z)) ≤ ε^{β⁺}` for all `z ∈ B_1`;
* (eq:ann-volume) for each `0 < r₁ < r₂` there are constants `C₁, C₂ > 0` such that, with polynomially high
  probability as `ε → 0`, `C₂ ε^{β⁻} ≤ μ_h(𝔸_{r₁ε, r₂ε}(z)) ≤ C₁ ε^{β⁺}` for all `z ∈ B_1`.

The annulus bound is uniform in `z ∈ B_1` on the good event, as the paper's derivation from eq:ball-volume gives. The
exponent `γ(Q-α₀)` is the scaling exponent of `μ_h(B_ε(0))` (from the log singularity `-α₀ log |·|`); for
`|z| ≍ ε^s`, `s ∈ [0, 1]`, the exponent of `μ_h(B_ε(z))` ranges over convex combinations of `(2∓γ)²/2` and
`γ(Q-α₀)`, whence the ranges of [C1]. For `α₀ ∈ [-2, 2]` they are the printed ranges. -/
def LiouvilleVolumeGrowthStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ βplus βminus : ℝ, 0 < βplus → βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    PolyHighProb P (fun ε => {ω | ∀ z ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal (ε ^ βminus) ≤ μ ω (ball z ε) ∧ μ ω (ball z ε) ≤ ENNReal.ofReal (ε ^ βplus)}) ∧
    ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      PolyHighProb P (fun ε => {ω | ∀ z ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal (C₂ * ε ^ βminus) ≤ μ ω (annulus z (r₁ * ε) (r₂ * ε)) ∧
          μ ω (annulus z (r₁ * ε) (r₂ * ε)) ≤ ENNReal.ofReal (C₁ * ε ^ βplus)})

/-! ### Unnumbered consequences: full support (I1) and volume growth at all small scales (I2) -/

/-- Input I1 (docs/campaign/GRAPH.md; stated informally at lines 134-135, used in Sections 4, 5 and 9): almost surely
`μ_h(U) > 0` for every nonempty open `U ⊆ ℂ`. It is a consequence, not a literature input: it follows from the lower
bound of `LQGVolumeGrowthAllScalesStmt` (every nonempty open `U` contains a ball `B_r(z)` with `z ∈ B_R` and `r < r₀`),
which itself follows from Lemma 2.4; see HarmonicBalls/Proposed/LQG.lean, `WholePlaneLQGBallMassBounds`, for the
derivation from a single published estimate. -/
def LQGMeasureFullSupportStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U

/-- Input I2 (docs/campaign/GRAPH.md): the hypothesis eq:volume-growth (line 3527, with [C2]) of Appendix A holds for
`μ_h` almost surely, at all small scales and for every `R > 0`: a.s., for every `R > 0`, every
`β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})` and every `β⁻ > max {(2+γ)²/2, γ(Q-α₀)}` (ranges of [C1]) there is `r₀ > 0`
with `r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` for all `r ∈ (0, r₀)` and `z ∈ B_R`. The paper derives it from Lemma 2.4 and the
scaling properties of `h` and `μ_h` (eq:h-coordinate-change, eq:measure-coord; lines 3529-3530): Borel-Cantelli over
the dyadic scales `ε = 2^{-k}`, monotonicity of `r ↦ μ_h(B_r(z))` and the slack in the open exponent ranges; a countable
family of radii and exponents gives one event for all of them. It is a consequence, not a literature input. -/
def LQGVolumeGrowthAllScalesStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus →
    βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ βminus) ≤ μ ω (ball z r) ∧ μ ω (ball z r) ≤ ENNReal.ofReal (r ^ βplus)

/-! ### Proposition 2.5: expected exit time of LBM and Green potentials of `μ_h` -/

open scoped ContDiff in
/-- `O` is a *smooth bounded open set* (Proposition 2.5, line 525): `O` is bounded and has a `C^∞` defining function,
i.e. `O = {ρ < 0}` for some `ρ ∈ C^∞(ℂ, ℝ)` whose differential does not vanish on `{ρ = 0}` (then `{ρ = 0} = ∂O`).
This is the usual notion of a bounded open set with `C^∞` boundary (equivalently, `∂O` is locally the graph of a
`C^∞` function with `O` on one side, as in Gilbarg-Trudinger §6.2); `O` need not be connected. -/
def IsSmoothBoundedOpen (O : Set ℂ) : Prop :=
  Bornology.IsBounded O ∧
    ∃ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ ∧ O = {z | ρ z < 0} ∧ ∀ z, ρ z = 0 → fderiv ℝ ρ z ≠ 0

/-- Proposition 2.5 (prop:lbm-exit-time, line 524). Almost surely, for every smooth bounded open set `O`:

* (LBM clause) if `F ω x` is the LQG clock of planar Brownian motion started from `x` for the field `h(ω)` (a.s. for
  all `x`), the expected exit time `E_x[τ_O]` of LBM from `O` started at `x ∈ O` is finite and Hölder continuous in
  `x ∈ O`;
* (Green clause) more generally, for every `f ∈ L^∞(closure O)` (essentially bounded with respect to `μ_h`, the
  measure of the integral), `q(x) = ∫_O G_O(x,y) f(y) μ_h(dy)` is finite (the integral converges absolutely) for
  every `x ∈ closure O` and is Hölder continuous on `closure O`.

Only the LBM clause is under the clock hypothesis; the Green clause does not involve LBM and is stated without it
(operator 2026-11-03 04:45, fix (5)). The Green clause is exactly `GreenPotentialHolderStmt`.

The paper's statement omits "almost surely" (GRAPH.md, Prop. 2.5); the a.s. event is taken uniform in `O` and `f`,
as the proof (from the a.s. volume growth bound I2) gives. Junk values: `greenFunction O x x = 0` is irrelevant since
`μ_h` has no atoms, and `q = 0` on `∂O`, where `G_O(x,·) = 0`.

The LBM clause is a quoted result whose cited sources do not cover the scope the paper needs [NCS1]: it is drafted as
printed and not consumed. The paper consumes only the Green clause, stated without LBM as `GreenPotentialHolderStmt`
(operator decision E26). -/
def GreenPotentialLiouvilleHolderStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  (∀ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
    (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) →
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
        ∃ C r : ℝ≥0, 0 < r ∧ HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O) ∧
  ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
    ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O)

/-- Proposition 2.5 (prop:lbm-exit-time, line 524), Green-potential clause. Almost surely, for every smooth bounded
open set `O` and every `f ∈ L^∞(closure O)` (essentially bounded with respect to `μ_h` on `closure O`), the Green
potential `q(x) = ∫_O G_O(x,y) f(y) μ_h(dy)` is finite (the integral converges absolutely) for every `x ∈ closure O`
and is Hölder continuous on `closure O`.

This is the second clause of `GreenPotentialLiouvilleHolderStmt`, which states it without the clock hypothesis of
the LBM clause (the clause does not involve Liouville Brownian motion). It is the only part of Proposition 2.5 that
the paper consumes: Prop 4.1 (line 710), Lemma 4.2 (line 732), Section 6 (line 1138), Appendix A property 1 of `q`
(line 3543); GRAPH.md entry 2.5; operator decision E26. The LBM clause of Proposition 2.5 and Proposition 2.6 are
quoted results whose cited sources do not cover the scope the paper needs (Berestycki 2015, Thm 1.2, is annealed and
for one start; Garban-Rhodes-Vargas 2016, Thm 2.7, is for the massive whole-plane GFF; Kigami 2019, Thm 13.1, does
not identify its process with LBM) [NCS1]. They stay drafted as printed and unconsumed.
`greenPotentialLiouvilleHolderStmt_green` derives this statement from the printed one (its second conjunct). The
a.s. event is uniform in `O` and `f`; junk values as in `GreenPotentialLiouvilleHolderStmt`. -/
def GreenPotentialHolderStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
    ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧
        HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O)

universe u

/-- The printed Proposition 2.5 implies its Green-potential clause `GreenPotentialHolderStmt`: it is the second
conjunct, which carries no clock hypothesis (fix (5) of 2026-11-03; an earlier version put both clauses under the
clock premise, and this lemma then needed an LQG clock from every start, outside the scope of the cited sources
[NCS1]). The proof consumes `GreenPotentialHolderStmt` directly. -/
theorem greenPotentialLiouvilleHolderStmt_green (h : GreenPotentialLiouvilleHolderStmt.{u}) :
    GreenPotentialHolderStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hLQG
  exact (h γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hLQG).2

/-! ### Proposition 2.6: the heat kernel of reflected LBM in a square -/

/-- Proposition 2.6 (prop:lbm-continuity, line 554), with correction [C5]. Let `K = closedSquare a L` (`L > 0`) and
let `F ω x` be the LQG clock of Brownian motion reflected in `K` (`reflectedPlanarBrownianMotion a L`) started from
`x ∈ K`, for the field `h(ω)`. Almost surely, the heat kernel `p^K_t(x,y)` of γ-LBM with Neumann (reflecting) boundary
conditions on `K` exists (`IsLBMHeatKernel`: `P[𝓑^x_t ∈ dy | h] = p^K_t(x,y) μ_h(dy)` on `K`, eq:defining-property-of-
kernel with [C5]), is finite (real-valued), jointly continuous on `(0,∞) × K × K`, and strictly positive there.

"A square" is read as a closed axis-parallel square, as for all squares of the paper (e.g. line 1223, the dyadic
squares of Section 11) and for the unit square of Kigami 2019; reflected Brownian motion in a square is the folded
planar Brownian motion of HarmonicBalls/Defs/LBM.lean.

A quoted result whose cited source does not cover the scope the paper needs [NCS1]: drafted as printed and not
consumed (Lemma 6.4 is proved without it, docs/campaign/E19-route-b.md §1.3). -/
def ReflectedLBMHeatKernelStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ (a : ℂ) (L : ℝ), 0 < L →
  ∀ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
    (∀ᵐ ω ∂P, ∀ x ∈ closedSquare a L,
      IsLQGClock (reflectedPlanarBrownianMotion a L) γ (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) →
  ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ → ℂ → ℝ,
    IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) (F ω) (closedSquare a L) (μ ω) p ∧
    ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) ∧
    ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare a L, ∀ y ∈ closedSquare a L, 0 < p t x y

end HarmonicBalls
