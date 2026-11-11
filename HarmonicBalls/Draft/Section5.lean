import Mathlib.Probability.IdentDistrib
import HarmonicBalls.Draft.Section1
import HarmonicBalls.Draft.Section4

/-!
# Section 5: statements of Propositions 5.1-5.4, Theorem 5.5, Proposition 5.6 and Lemmas 5.7-5.8

Statements of the numbered results of Section 5 (sec:non-degenerate, lines 805-1047) of the corrected draft: the
properties of the clusters `Λ^z_t` of the unit ball (Propositions 5.1-5.3, proved in Sections 7-8), the
regularized clusters `Λ̂^z_t = int(closure Λ^z_t)` (eq:regular-cluster, line 846) and their harmonic ball properties
up to a time `T` (Proposition 5.4), the whole-plane family of Theorem 5.5 and its uniqueness (Proposition 5.6, proved
in Section 9), the scale invariance of clusters (Lemma 5.7) and the strong compatibility with clusters of general
bounded open sets (Lemma 5.8).

## Random setting

As in `Draft/Section3.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`) and a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`), where `h = h^ℂ - α₀ log |·|`. "On an event of probability 1" is `∀ᵐ ω ∂P`.

## The family of Theorem 5.5

Proposition 5.6 and Lemma 5.8 speak of "the" family `{Λ̂_t(z)}_{t > 0, z ∈ ℂ}` given by Theorem 5.5. They are stated
for an arbitrary random family `Λ̂ : Ω → ℂ → ℝ → Set ℂ` which almost surely, for every `z`, has the properties
asserted by Theorem 5.5 (`IsRegularizedClusterFamily`). The last of these properties,
`Λ̂_t(z) = int(closure Λ_{B_r;z}(t))` for all `r ≥ s` whenever `closure Λ̂_t(z) ⊆ B_s`, determines `Λ̂_t(z)` (it is
bounded), so any such family is almost surely the family of Theorem 5.5.

## Conventions

* `Λ^z_t = cluster μ 1 z t`, the cluster of the unit ball (line 601); `B_s` is centred at `0`; `∂B_1 = sphere 0 1`.
* "`A ⋐ B_s`" (compactly contained) is `closure A ⊆ ball 0 s`.
* "Satisfying the conditions of Theorem 1.1" (Proposition 5.4, Theorem 5.5) is `SatisfiesHarmonicBallConditions`
  of `Draft/Section1.lean` (conditions (a)-(b)), restricted to `0 < t < T` in Proposition 5.4
  (`SatisfiesHarmonicBallConditionsOn`). "Harmonic balls satisfying the assumptions in Theorem 1.1"
  (Proposition 5.6) is `IsHarmonicBallFamily`.

## Corrections applied

[C58] (Proposition 5.4, lines 853-856: `T = T(z) > 0` depends on `z`; the idle binder "for all `r > 0`" is deleted;
ESCALATIONS E10, docs/campaign/GRAPH.md F4, G6). [C6], [C7] through `SatisfiesHarmonicBallConditions` and
`IsHarmonicBallFamily`. Readings of misprints, each flagged in the docstring and reported (not yet in
`~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`): Proposition 5.2 (line 832, `B_ε(z)` read `B_ε`), Proposition 5.3
(line 837, `B_r(z)` with `r` free read `B_1`, GRAPH S1).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set ProbabilityTheory
open scoped Pointwise Topology

/-! ## Regularized clusters and the conditions of Theorem 1.1 up to a time `T` -/

/-- The *regularized cluster* `Λ̂_{B_r;z}(t) = int(closure Λ_{B_r;z}(t))` (eq:regular-cluster, line 846, stated there
for `r = 1`; Theorem 5.5, line 867, uses it for `B_r`). -/
def regularizedCluster (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) : Set ℂ :=
  interior (closure (cluster μ r z t))

/-- The conditions (a)-(b) of Theorem 1.1 (theorem:harmonic-balls, lines 152-160) for a family `{Λ_t}_{0 < t < T}`
indexed by the interval `(0, T)` (Proposition 5.4, line 855: "satisfying the conditions of Theorem 1.1 for
`0 < t < T`"): the fields of `SatisfiesHarmonicBallConditions` with `t > 0` replaced by `t ∈ (0, T)`, and
`⋂_{0 < t < T} Λ_t = {z}`. -/
structure SatisfiesHarmonicBallConditionsOn (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ) (T : ℝ) : Prop where
  /-- (a) `μ(Λ_t) = t`. -/
  measure_eq : ∀ t ∈ Ioo 0 T, μ (Λ t) = ENNReal.ofReal t
  /-- (a) `μ(∂Λ_t) = 0` (correction [C6]). -/
  measure_frontier : ∀ t ∈ Ioo 0 T, μ (frontier (Λ t)) = 0
  /-- (a) `Λ_t` is equal to the interior of its closure. -/
  isRegularOpen : ∀ t ∈ Ioo 0 T, IsRegularOpen (Λ t)
  /-- (b) `Λ_t` is bounded. -/
  isBounded : ∀ t ∈ Ioo 0 T, Bornology.IsBounded (Λ t)
  /-- (b) `Λ_t` is connected. -/
  isConnected : ∀ t ∈ Ioo 0 T, IsConnected (Λ t)
  /-- (b) `Λ_t` contains `z`. -/
  mem : ∀ t ∈ Ioo 0 T, z ∈ Λ t
  /-- (b) `Λ_t` increases in `t`. -/
  monotoneOn : MonotoneOn Λ (Ioo 0 T)
  /-- (b) `Λ_t` is continuous in `t` for the Hausdorff topology. -/
  hausdorffContinuousOn : HausdorffContinuousOn Λ (Ioo 0 T)
  /-- (b) `⋂_{0 < t < T} Λ_t = {z}`. -/
  iInter_eq : ⋂ t ∈ Ioo (0 : ℝ) T, Λ t = {z}

/-- The properties of the family `{Λ̂_t(z)}_{t > 0}` asserted by Theorem 5.5
(theorem:full-theorem-minus-uniqueness, lines 863-868) for the measure `μ` and the centre `z`: it satisfies the
conditions (a)-(b) of Theorem 1.1 (`SatisfiesHarmonicBallConditions`), each `Λ̂_t(z)`, `t > 0`, is a subharmonic
ball centred at `z` (`IsSubharmonicBall`, eq:subharmonic-ball), and whenever `Λ̂_t(z) ⋐ B_s` for some `s > 0`,
`Λ̂_t(z) = int(closure Λ_{B_r;z}(t))` (`regularizedCluster μ r z t`) for all `r ≥ s` (line 867). -/
def IsRegularizedClusterFamily (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ) : Prop :=
  SatisfiesHarmonicBallConditions μ Λ z ∧ (∀ t : ℝ, 0 < t → IsSubharmonicBall μ (Λ t) z) ∧
    ∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r →
      Λ t = regularizedCluster μ r z t

/-! ## Clusters of general open sets (lines 1014-1015) -/

/-- The supersolutions `S_{U;z}(t)` of the obstacle problem in an open set `U` (line 1015: "the definition of
`Λ_{B_r;z}(t)` ... extend[s] essentially verbatim to the case when `B_r` is replaced by any bounded open set"):
eq:super-solutions (line 583) with `B_r` replaced by `U`, i.e. functions continuous on `closure U` with `Δw ≤ μ` in `U`
and `w ≥ -t G_U(z,·)` on `closure U` off the pole (as in `supersolutions`).

On `∂U` the junk value `greenFunction U z x = 0` (`x ∉ U`) is the boundary value of `G_U(z,·)` at regular boundary
points, e.g. for Lipschitz `U`; at irregular boundary points the paper's "verbatim" extension is ambiguous
(docs/campaign/GRAPH.md G9). -/
def supersolutionsOn (μ : Measure ℂ) (U : Set ℂ) (z : ℂ) (t : ℝ) : Set (ℂ → ℝ) :=
  {w | ContinuousOn w (closure U) ∧ LaplacianLE w μ U ∧
    ∀ x ∈ closure U, x ≠ z → -t * greenFunction U z x ≤ w x}

/-- The least supersolution `v_{U;z}(t)` in an open set `U` (eq:least-super-solution, line 588, with `B_r` replaced
by `U`, line 1015): the pointwise infimum of `S_{U;z}(t)`, with the junk conventions of `leastSupersolution`. -/
noncomputable def leastSupersolutionOn (μ : Measure ℂ) (U : Set ℂ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)

/-- The cluster `Λ_{U;z}(t)` of an open set `U` (eq:non-co-set, line 592, with `B_r` replaced by `U`, line 1015):
`{x ∈ U : v_{U;z}(t)(x) > -t G_U(z,x)}`, together with the pole (as in `cluster`). Meaningful for `z ∈ U`. -/
def clusterOn (μ : Measure ℂ) (U : Set ℂ) (z : ℂ) (t : ℝ) : Set ℂ :=
  {x ∈ U | x = z ∨ -t * greenFunction U z x < leastSupersolutionOn μ U z t x}

/-! ## Statements -/

/-- Proposition 5.1 (prop:upper-bound, line 815). On an event of probability 1, there is a random
`T = T(γ, h) > 0` such that `closure Λ^z_t ⊆ B_1` for each `z ∈ B_{1/2}` and all `0 < t < T`.
Corrections applied: none ([C3] through `cluster`). -/
def ClusterUpperBoundStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t → t < T →
    closure (cluster (μ ω) 1 z t) ⊆ ball 0 1

/-- Proposition 5.2 (prop:continuity, line 824). On an event of probability 1, for all `z ∈ B_{1/2}`:
`⋂_{t > 0} closure Λ^z_t = {z}` (eq:contains-origin, line 826), and for each `t > 0`, for all sufficiently small
`ε > 0` there is `δ > 0` with `closure Λ^z_{t'} ⊆ Λ^z_t + B_ε` for all `t' ∈ [t, t + δ]` (eq:continuity, line 831).

* "For all `ε > 0` sufficiently small" is `∃ ε₀ > 0, ∀ ε ∈ (0, ε₀)`; `δ = δ(z)` also depends on `t` and `ε`.
* `Λ^z_t + B_ε` is the Minkowski sum with the ball `B_ε = B_ε(0)`, the `ε`-neighbourhood of `Λ^z_t`. The paper prints
  `Λ^z_t + B_ε(z)` (line 832), which translates the neighbourhood by `z`. Read literally the claim is false for every
  `z ≠ 0`: by eq:contains-origin and compactness, `closure Λ^z_t ⊆ B_{|z|/2}(z)` for small `t`, so for
  `ε < |z|/2` the set `Λ^z_t + B_ε(z) ⊆ B_{|z|}(2z)` misses `z ∈ closure Λ^z_{t'}`. Reported as a misprint.
* The proof (Proposition 7.2, line 2104) covers only `t` with `Λ^z_t ⋐ B_1`; later `t` are unproved
  (docs/campaign/GRAPH.md G12). Corrections applied: the reading `B_ε(z) → B_ε` above. -/
def ClusterContinuityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2),
    ⋂ t ∈ Ioi (0 : ℝ), closure (cluster (μ ω) 1 z t) = {z} ∧
    ∀ t : ℝ, 0 < t → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧ ∀ t' ∈ Icc t (t + δ),
      closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε

/-- Proposition 5.3 (prop:boundary-measure, line 836). On an event of probability 1, `μ_h(∂Λ^z_t) = 0` for all
`z ∈ B_1` and `t > 0` such that `closure Λ^z_t ⊆ B_1`.

The paper prints the hypothesis as `closure Λ^z_t ⊂ B_r(z)` (line 837) with `r` bound nowhere; it is read as
`closure Λ^z_t ⊆ B_1`, the hypothesis `Λ^z_t ⋐ B_1` of Proposition 8.1 (prop:boundary-measure-zero, line 2125), which
is the proof of this proposition (docs/campaign/GRAPH.md S1). Corrections applied: this reading. -/
def ClusterBoundaryMeasureZeroStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    μ ω (frontier (cluster (μ ω) 1 z t)) = 0

/-- Proposition 5.4 (prop:conditional, line 853), with correction [C58]. On an event of probability 1, for all
`z ∈ B_{1/2}` there is `T = T(z) > 0` such that the regularized clusters `Λ̂^z_t = int(closure Λ^z_t)`
(eq:regular-cluster, line 846), `0 < t < T`, are compactly contained in `B_1` and satisfy the conditions of
Theorem 1.1 for `0 < t < T` (`SatisfiesHarmonicBallConditionsOn`), and `closure Λ̂^z_T ∩ ∂B_1 ≠ ∅`.

* [C58] (ESCALATIONS E10, docs/campaign/GRAPH.md F4): the printed statement binds "for all `r > 0`", which occurs
  nowhere, and leaves `T` unbound. `T` is existentially quantified after `z`: with the uniform `T` of
  Proposition 5.1 the last claim would force all exit times from `B_1` of centres in `B_{1/2}` to coincide, which
  fails already for Lebesgue measure (exit time `π(1 - |z|)²`).
* "Strictly contained in `closure B_1`" (line 855) is read as `Λ̂^z_t ⋐ B_1`, i.e. `closure Λ̂^z_t ⊆ B_1`, the
  conclusion of Proposition 5.1 from which it is derived (lines 848-850).
* The text before the statement (lines 848-850) also derives that `Λ̂^z_t` is a subharmonic ball; the printed
  statement does not include it. -/
def RegularizedClusterHarmonicBallsStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∃ T : ℝ, 0 < T ∧
    (∀ t ∈ Ioo 0 T, closure (regularizedCluster (μ ω) 1 z t) ⊆ ball 0 1) ∧
    SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z T ∧
    (closure (regularizedCluster (μ ω) 1 z T) ∩ sphere (0 : ℂ) 1).Nonempty

/-- Theorem 5.5 (theorem:full-theorem-minus-uniqueness, line 863). On an event of probability 1, for all `z ∈ ℂ`
there is a family `{Λ̂_t(z)}_{t > 0}` satisfying the conditions of Theorem 1.1; moreover each `Λ̂_t(z)` is a
subharmonic ball (centred at `z`), and if `Λ̂_t(z) ⋐ B_s` for some `s > 0`, then
`Λ̂_t(z) = int(closure Λ_{B_r;z}(t))` for all `r ≥ s` (`IsRegularizedClusterFamily`).

The quantifier order of the paper is kept: `∀ᵐ ω ∂P, ∀ z, ∃ family`. In the last clause `t > 0` is implicit in the
paper ("each cluster"). Corrections applied: [C6] through `SatisfiesHarmonicBallConditions`. The proof (lines
951-1009) needs repairs (docs/campaign/GRAPH.md G6, G7). -/
def ExistenceHarmonicBallsStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ Λ : ℝ → Set ℂ, IsRegularizedClusterFamily (μ ω) Λ z

/-- Proposition 5.6 (prop:uniqueness, line 872). Let `{Λ̂_t(z)}_{t > 0, z ∈ ℂ}` be given by Theorem 5.5. On an event
of probability 1, if for some `z ∈ ℂ` a family `{A_t(z)}_{t > 0}` of harmonic balls satisfies the assumptions of
Theorem 1.1, then `A_t(z) = Λ̂_t(z)` for all `t > 0`.

`Λ̂` is any random family which almost surely, for every `z`, has the properties of Theorem 5.5
(`IsRegularizedClusterFamily`; see the module docstring). "Harmonic balls satisfying the assumptions in
Theorem 1.1" is `IsHarmonicBallFamily` (harmonic balls for the enlarged test class of lines 136-146, which the
uniqueness proof uses through Lemma 9.1(2)). Corrections applied: [C6], [C7] through `IsHarmonicBallFamily`. -/
def UniquenessHarmonicBallsStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) →
  ∀ᵐ ω ∂P, ∀ (z : ℂ) (A : ℝ → Set ℂ), IsHarmonicBallFamily (μ ω) A z → EqOn A (Λhat ω z) (Ioi 0)

/-- Lemma 5.7 (lemma:scale-invariance-flow, line 885). For each `k > 0` and `z ∈ B_1`, the laws of
`{Λ^z_t}_{t > 0}` and `{k⁻¹ Λ_{B_k;kz}(A_k t)}_{t > 0}` coincide, where `A_k = e^{γ(Q log k + h_k(0))}` and `h_k(0)`
is the circle average of `h` on `∂B_k(0)` (`fieldCircleAverage`).

* "The laws coincide" (docs/campaign/GRAPH.md G11) is `IdentDistrib` of the two random families
  `ω ↦ (t ↦ Λ_t)`, indexed by `t ∈ (0, ∞)`, valued in `Ioi 0 → Set ℂ` with Mathlib's product σ-algebra
  (`Set.instMeasurableSpace`: the events `{x ∈ Λ_t}`, i.e. the finite-dimensional laws of the indicator field
  `(t, x) ↦ 1{x ∈ Λ_t}`). `IdentDistrib` includes that both families are random variables (a.e. measurable), which
  "the law" presupposes.
* The statement is for a fixed centre `z`, as printed. The proof of Theorem 5.5 (lines 952-955) applies it
  simultaneously to all centres `x ∈ B_{1/2}`; what the proof of Lemma 5.7 establishes (lines 905-938) is the
  pathwise identity `Λ^z_t(h') = k⁻¹ Λ_{B_k;kz}(A_k t)(h)` for `h' = h(k·) - h_k(0)`, valid for all `z` and `t`
  at once. -/
def ClusterScaleInvarianceStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ k : ℝ, 0 < k → ∀ z ∈ ball (0 : ℂ) 1,
    IdentDistrib (fun ω (t : Ioi (0 : ℝ)) => cluster (μ ω) 1 z t)
      (fun ω (t : Ioi (0 : ℝ)) => k⁻¹ • cluster (μ ω) k (k • z)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)) P P

/-- Lemma 5.8 (lemma:strong-compatibility, line 1019). Let `U` be a deterministic bounded open set and let
`{Λ̂_t(z)}` be given by Theorem 5.5. On an event of probability 1, for all `t > 0` and `z ∈ U`,
`closure Λ̂_t(z) = closure Λ_{U;z}(t)` if either `Λ̂_t(z) ⋐ U` or `Λ_{U;z}(t) ⋐ U`.

* `Λ_{U;z}(t)` is `clusterOn μ U z t` (line 1015). "On an event of probability 1" is implicit in the printed
  statement (both families are random); `U` is fixed before the event, as "deterministic" says.
* The printed statement has `z ∈ ℂ`; `Λ_{U;z}(t)` is defined only for a pole `z ∈ U` (and `Λ̂_t(z) ⋐ U` forces
  `z ∈ U`), so `z ∈ U` is a hypothesis.
* The proof ("essentially verbatim", line 1015) uses continuity of `G_U` and `q_U` up to `∂U`, which holds for
  regular `U` but not for every bounded open `U` (docs/campaign/GRAPH.md G9). The statement is kept for every
  bounded open `U`, as printed. -/
def ClusterStrongCompatibilityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λhat : Ω → ℂ → ℝ → Set ℂ, (∀ᵐ ω ∂P, ∀ z : ℂ, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z) →
  ∀ U : Set ℂ, IsOpen U → Bornology.IsBounded U →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ U,
    (closure (Λhat ω z t) ⊆ U ∨ closure (clusterOn (μ ω) U z t) ⊆ U) →
      closure (Λhat ω z t) = closure (clusterOn (μ ω) U z t)

/-! ## Sanity lemmas -/

theorem isOpen_regularizedCluster (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) :
    IsOpen (regularizedCluster μ r z t) :=
  isOpen_interior

/-- The conditions of Theorem 1.1 for all `t > 0` give them for `0 < t < T`. -/
theorem SatisfiesHarmonicBallConditions.satisfiesHarmonicBallConditionsOn {μ : Measure ℂ} {Λ : ℝ → Set ℂ}
    {z : ℂ} {T : ℝ} (h : SatisfiesHarmonicBallConditions μ Λ z) (hT : 0 < T) :
    SatisfiesHarmonicBallConditionsOn μ Λ z T where
  measure_eq t ht := h.measure_eq t ht.1
  measure_frontier t ht := h.measure_frontier t ht.1
  isRegularOpen t ht := h.isRegularOpen t ht.1
  isBounded t ht := h.isBounded t ht.1
  isConnected t ht := h.isConnected t ht.1
  mem t ht := h.mem t ht.1
  monotoneOn := h.monotoneOn.mono Ioo_subset_Ioi_self
  hausdorffContinuousOn t ht ε hε :=
    nhdsWithin_mono _ Ioo_subset_Ioi_self (h.hausdorffContinuousOn t (Ioo_subset_Ioi_self ht) ε hε)
  iInter_eq := by
    apply Subset.antisymm
    · intro x hx
      rw [← h.iInter_eq]
      simp only [mem_iInter] at hx ⊢
      intro t ht
      rcases lt_or_ge t T with htT | hTt
      · exact hx t ⟨ht, htT⟩
      · have hT2 : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
        exact h.monotoneOn (Ioo_subset_Ioi_self hT2) ht (by linarith [hT2.2]) (hx _ hT2)
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      simp only [mem_iInter]
      exact fun t ht => h.mem t ht.1

/-- For a ball, the supersolutions of the general open set are those of Section 3.1. -/
theorem supersolutionsOn_ball (μ : Measure ℂ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) (t : ℝ) :
    supersolutionsOn μ (ball 0 r) z t = supersolutions μ r z t := by
  simp only [supersolutionsOn, supersolutions, closure_ball (0 : ℂ) hr]

/-- For a ball, the cluster of the general open set is the cluster of Section 3.1. -/
theorem clusterOn_ball (μ : Measure ℂ) {r : ℝ} (hr : r ≠ 0) (z : ℂ) (t : ℝ) :
    clusterOn μ (ball 0 r) z t = cluster μ r z t := by
  simp only [clusterOn, cluster, leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hr]

end HarmonicBalls
