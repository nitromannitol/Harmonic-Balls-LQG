import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.HarmonicBall

/-!
# Section 4: statements of Proposition 4.1 and Lemmas 4.2-4.3 (basic properties of clusters)

Statements of the numbered results of Section 4 (sec:basic-properties-cluster, lines 663-804) of the corrected draft:
the lower bound on clusters (Proposition 4.1), the Hölder continuity of the least supersolution (Lemma 4.2), and the
subharmonic ball property of non-degenerate clusters (Lemma 4.3), together with the definition of a *subharmonic ball*
(eq:subharmonic-ball, line 742; test functions eq:sub-harmonic-potential, line 746).

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`), where `h = h^ℂ - α₀ log |·|`. "On an event of probability 1" is
`∀ᵐ ω ∂P`; random quantities (`ε`, `t(δ)`, `t⁺`, `C`) are existentially quantified inside the almost sure event, and
the deterministic exponent of Lemma 4.2 outside it.

## Conventions

* Objects of the obstacle problem from `HarmonicBalls/Defs/Obstacle.lean`; the paper's `Λ^z_t`, `v^z_t` (no domain
  in the notation) are those of the unit ball `B_1` (line 601): `cluster μ 1 z t`, `leastSupersolution μ 1 z t`.
* Balls `B_s` without centre are centred at `0`; `∂B_1 = sphere 0 1`; `∂Λ = frontier Λ`.

## Corrections applied

[C8] (Lemma 4.2, lines 717, 722: the exponent is `α = α(γ, α₀) > 0`, printed `α(γ)`; ESCALATIONS E9,
docs/campaign/GRAPH.md F3). [C3] (pole `z`) through `cluster`, `leastSupersolution` of `Defs/Obstacle.lean`.
See `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-! ## Subharmonic balls (Section 4.3, lines 741-754) -/

/-- The *sub-mean-value property* of `f` on `Λ` at `z` for `μ` (eq:subharmonic-ball, line 742):
`f` is `μ`-integrable on `Λ` and `μ(Λ) f(z) ≤ ∫_Λ f dμ`. The companion of `HasMeanValueProperty`
(eq:harmonic-ball, line 78). -/
def HasSubMeanValueProperty (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) (f : ℂ → ℝ) : Prop :=
  IntegrableOn f Λ μ ∧ f z * μ.real Λ ≤ ∫ x in Λ, f x ∂μ

/-- The test functions of a subharmonic ball `Λ` centred at `z` (eq:sub-harmonic-potential, lines 746-751), finite
at the centre: the functions
`f(x) = ∫_O G_O(x,y) ν(dy) + q(x)`
where `O` is an open set containing (a neighbourhood of) `closure Λ`, `ν` is a signed Radon measure with compact
support in `O` and `ν|_Λ ≤ 0`, and `q` is harmonic on `O`.

* `ν = ν₁ - ν₂` (Jordan decomposition) with `ν₁, ν₂` finite measures concentrated on a compact `K ⊆ O`
  (as in `greenPotentialClass`); `ν|_Λ ≤ 0` is `ν₁(Λ) = 0`. Conversely every such difference has `ν|_Λ ≤ 0`.
* "`O` contains a neighbourhood of `closure Λ`" is `closure Λ ⊆ O` (`O` is open). `O` is not assumed bounded,
  as printed; `greenFunction O` is the Green function for Greenian `O` and the Newtonian kernel for non-Greenian `O`
  (`Defs/Green.lean`), which gives test functions of the same form on a large ball.
* *Finite at the centre.* The paper's `f` takes values in `[-∞, ∞)` (`G_O = +∞` on the diagonal, Proposition 2.3),
  e.g. `f = -G_O(·, x)`, `x ∈ Λ` (Lemma 9.1, line 2297). When `f(z) = -∞`, i.e. `ν₂({z}) > 0` or
  `∫ G_O(z,y) ν₂(dy) = +∞`, inequality eq:subharmonic-ball holds trivially (`μ(Λ) > 0`). The class keeps exactly
  the test functions with `f(z)` finite: `ν₂({z}) = 0` and `y ↦ G_O(z,y)` is `ν₂`-integrable. Then the value
  `f(z)` below is the paper's value (no diagonal junk at `z`). Elsewhere the junk values of `greenPotential`
  (non-integrability, atoms of `ν₂`) occur on a polar set together with the countably many atoms of `ν₂`, which
  `μ_h` does not charge almost surely. `ν₁` does not charge `Λ`, so `∫ G_O(x,y) ν₁(dy)` is finite for `x ∈ Λ`. -/
def subharmonicBallTestClass (Λ : Set ℂ) (z : ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (O K : Set ℂ) (ν₁ ν₂ : Measure ℂ) (q : ℂ → ℝ), IsOpen O ∧ closure Λ ⊆ O ∧ IsCompact K ∧ K ⊆ O ∧
    IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧ ν₁ Kᶜ = 0 ∧ ν₂ Kᶜ = 0 ∧ ν₁ Λ = 0 ∧
    InnerProductSpace.HarmonicOnNhd q O ∧ ν₂ {z} = 0 ∧ Integrable (greenFunction O z) ν₂ ∧
    f = q + greenPotential O ν₁ - greenPotential O ν₂}

/-- `Λ` is a *subharmonic ball centred at `z` with respect to `μ`* (eq:subharmonic-ball, line 742): `Λ` is an open
set and every test function `f` of eq:sub-harmonic-potential (`subharmonicBallTestClass`) satisfies
`μ(Λ) f(z) ≤ ∫_Λ f dμ` (with `f` integrable on `Λ`, `HasSubMeanValueProperty`).

As for `IsHarmonicBall` (eq:harmonic-ball, line 78) the definition includes `z ∈ Λ` ("centred at `z`") and
`0 < μ(Λ) < ∞`; the paper's remark at lines 753-754 ("every subharmonic ball is a harmonic ball") presupposes them,
and they hold for the clusters of Lemma 4.3 (`μ_h(Λ) = t`, Lemma 3.4). In the paper's terminology (Sakai,
Shahgholian-Sjödin) these are quadrature domains for subharmonic functions. -/
def IsSubharmonicBall (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  IsOpen Λ ∧ z ∈ Λ ∧ 0 < μ Λ ∧ μ Λ < ⊤ ∧
    ∀ f ∈ subharmonicBallTestClass Λ z, HasSubMeanValueProperty μ Λ z f

/-! ## Statements -/

/-- Proposition 4.1 (prop:lower-bound, line 673). On an event of probability 1, for each `z ∈ B_1`:
* for each `t > 0` there is a random `ε = ε(t) > 0` with `B_ε(z) ⊆ Λ^z_t`;
* for each `δ ∈ (|z|, 1)` there is a random `t(δ) > 0` with `B_{1-δ}(z) ⊆ Λ^z_t` for all `t ≥ t(δ)`;
* there is a random `t⁺ > 0` with `closure Λ^z_t ∩ ∂B_1 ≠ ∅` for all `t ≥ t⁺`.

Here `Λ^z_t = Λ_{B_1;z}(t)` (`cluster μ 1 z t`). Quantifier scope as printed: `ε` depends on `(t, z)`, `t(δ)` on
`(δ, z)`, and `t⁺` is introduced in the scope of `z` (the proof takes `t⁺ = μ_h(B_1)`, independent of `z`). The proof
of the last claim (lines 711-712) uses the equality case of Lemma 3.4, which needs `μ_h(∂Λ^z_t) = 0`; the claim
itself follows from the mass identity `t = μ_h(Λ) + ν(∂Λ)` (docs/campaign/GRAPH.md G3). Corrections applied: none
([C3] through `cluster`). -/
def ClusterLowerBoundStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
    (∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧ ball z ε ⊆ cluster (μ ω) 1 z t) ∧
    (∀ δ ∈ Ioo ‖z‖ 1, ∃ tδ : ℝ, 0 < tδ ∧ ∀ t : ℝ, tδ ≤ t → ball z (1 - δ) ⊆ cluster (μ ω) 1 z t) ∧
    (∃ tplus : ℝ, 0 < tplus ∧ ∀ t : ℝ, tplus ≤ t →
      (closure (cluster (μ ω) 1 z t) ∩ sphere (0 : ℂ) 1).Nonempty)

/-- Lemma 4.2 (odometer:cont, line 721). There is a deterministic exponent `α = α(γ, α₀) > 0` such that, on an
event of probability 1, there is a constant `C > 0` with
`|v^z_t(x) - v^z_t(y)| ≤ C |x - y|^α` for all `t > 0`, `z ∈ B_1` and `x, y ∈ B_1`,
where `v^z_t = v_{B_1;z}(t)` is the least supersolution (`leastSupersolution μ 1 z t`, eq:least-super-solution).

The exponent is chosen before the probability space (it depends only on `γ, α₀`); the constant `C` is random and
uniform in `t, z, x, y`. Corrections applied: [C8] (lines 717, 722: printed `α = α(γ)`; the exponent cannot be
uniform in `α₀`, since near the origin the oscillation of `v` on `B_s(0)` is of order `μ_h(B_{s/2}(0))`, roughly
`s^{γ(Q - α₀)}`; ESCALATIONS E9, docs/campaign/GRAPH.md F3). The paper prints no sign condition on `α`; `0 < α`
is part of [C8] (for `α ≤ 0` the bound is only boundedness). The uniformity of `C` in `t` and `z` needs a
quantitative form of Proposition 2.5 (GRAPH G4). -/
def LeastSupersolutionHolderStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∃ α : ℝ, 0 < α ∧
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, ∀ x ∈ ball (0 : ℂ) 1, ∀ y ∈ ball (0 : ℂ) 1,
      |leastSupersolution (μ ω) 1 z t x - leastSupersolution (μ ω) 1 z t y| ≤ C * ‖x - y‖ ^ α

/-- Lemma 4.3 (lemma:harmonic-ball, line 755). On an event of probability 1, for all `r, t > 0` and `z ∈ B_r`, if
`closure Λ_{B_r;z}(t) ⊆ B_r` and `μ_h(∂Λ_{B_r;z}(t)) = 0`, then `Λ_{B_r;z}(t)` is a subharmonic ball centred at `z`
(eq:subharmonic-ball, line 742; `IsSubharmonicBall`, with the test functions of eq:sub-harmonic-potential).

The printed conclusion "is a subharmonic ball" leaves the centre implicit; it is the pole `z` (proof, lines
764-786). The proof (lines 781-786) needs the identity `t G_O(z,·) - ∫_Λ G_O(y,·) μ_h(dy) = u` on all of `O`
(docs/campaign/GRAPH.md G5). Corrections applied: none ([C3] through `cluster`). -/
def ClusterSubharmonicBallStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ r t : ℝ, 0 < r → 0 < t → ∀ z ∈ ball (0 : ℂ) r,
    closure (cluster (μ ω) r z t) ⊆ ball 0 r → μ ω (frontier (cluster (μ ω) r z t)) = 0 →
      IsSubharmonicBall (μ ω) (cluster (μ ω) r z t) z

/-! ## Sanity lemmas -/

/-- The zero function is a test function of every subharmonic ball (`O = ℂ`, `ν = 0`, `q = 0`). -/
theorem zero_mem_subharmonicBallTestClass (Λ : Set ℂ) (z : ℂ) : (0 : ℂ → ℝ) ∈ subharmonicBallTestClass Λ z := by
  refine ⟨univ, ∅, 0, 0, 0, isOpen_univ, subset_univ _, isCompact_empty, empty_subset _, inferInstance,
    inferInstance, rfl, rfl, rfl, fun x _ => ?_, rfl, integrable_zero_measure, ?_⟩
  · exact InnerProductSpace.harmonicAt_const 0
  · ext x
    simp [greenPotential]

/-- Harmonic functions on an open `O ⊇ closure Λ` are test functions of a subharmonic ball (`ν = 0`). -/
theorem mem_subharmonicBallTestClass_of_harmonicOnNhd {Λ O : Set ℂ} {z : ℂ} {q : ℂ → ℝ} (hO : IsOpen O)
    (hΛO : closure Λ ⊆ O) (hq : InnerProductSpace.HarmonicOnNhd q O) : q ∈ subharmonicBallTestClass Λ z := by
  refine ⟨O, ∅, 0, 0, q, hO, hΛO, isCompact_empty, empty_subset _, inferInstance, inferInstance, rfl, rfl, rfl,
    hq, rfl, integrable_zero_measure, ?_⟩
  ext x
  simp [greenPotential]

/-- A subharmonic ball satisfies the sub-mean-value property for functions harmonic on an open neighbourhood of
its closure. -/
theorem IsSubharmonicBall.hasSubMeanValueProperty_of_harmonicOnNhd {μ : Measure ℂ} {Λ O : Set ℂ} {z : ℂ}
    {q : ℂ → ℝ} (h : IsSubharmonicBall μ Λ z) (hO : IsOpen O) (hΛO : closure Λ ⊆ O)
    (hq : InnerProductSpace.HarmonicOnNhd q O) : HasSubMeanValueProperty μ Λ z q :=
  h.2.2.2.2 q (mem_subharmonicBallTestClass_of_harmonicOnNhd hO hΛO hq)

end HarmonicBalls
