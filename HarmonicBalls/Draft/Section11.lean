import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.Green
import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Draft.Section1

/-!
# Section 11: statements of Propositions 11.2, 11.9, 11.11 and Lemmas 11.5-11.8, 11.10, 11.12-11.17

Statements of the numbered results of Section 11 (sec:novelty, lines 2697-3519 of the corrected draft): harmonic
balls are not Lipschitz domains (Section 11.1) and not LQG metric balls (Sections 11.2-11.3). Definitions 11.1, 11.3,
11.4, cones, rescaled sets, dyadic squares and the pinch-point configuration are in `HarmonicBalls/Defs/Geometry.lean`;
the LQG metric `D_h`, internal metrics and metric balls in `HarmonicBalls/Defs/LQGMetric.lean`.

## Random setting

As in `Draft/Section1.lean`: each statement quantifies over `0 < γ < 2`, `α₀ < Q = lqgQ γ`, a probability space
`(Ω, P)`, a whole-plane GFF `h^ℂ` (`IsWholePlaneGFF P hC hcirc`), a random measure `μ` with `μ ω = μ_h`
(`IsLQGMeasureOfField P γ α₀ hcirc μ`) and, when `D_h` enters, a random function `D` with `D ω = D_h`
(`IsLQGMetricOfField P γ ξ α₀ hC D`, `ξ` universally quantified as in Theorem 1.2). Lemma 11.12 and the auxiliary
Lemmas 11.15-11.17 of its proof are in the case `α₀ = 0` (line 3137). "With positive probability" and the lower bound
"`P[E] ≥ p`" are in inner-measure form (operator 2026-11-03 04:45, fix (3); as in the rigidity formalization): the event
`E` contains a measurable event `A` with `0 < P A` (resp. `p ≤ P A`), `∃ A ⊆ E, MeasurableSet A ∧ 0 < P A`. The events
need not be shown measurable; the outer measure `P E` would give a weaker statement.

## Objects defined here

* `annulusGreenPotentialSup μ x₀ a b` is `SG_{a,b}(x₀)` (eq:alternate-size-2-full, line 1140), defined in
  `HarmonicBalls/Defs/Annuli.lean` with the other annulus objects shared with Sections 6 and 8; Section 11 uses
  `SG_{3r,6r}(z)`.
* `coneMassEvent` is `G̃_r(z; M, 𝒬)` (eq:mu-h-wild, line 2793), `pinchPointEvent` is `Ĝ_r(z; M)`
  (eq:pinch-point-event, line 3124), `internalDiam` is `diam^δ_h` (line 3252), `pinchFirstEvent`, `pinchSecondEvent`,
  `pinchThirdEvent` are `Ẽ₁`, `Ẽ₂(M)`, `Ẽ₃` (eq:first-event, eq:second-event, eq:third-event, lines 3257-3273), and
  `IsPinchPointProofConfiguration` collects the requirements on `T, U, V, W, Q', Q, δ₀` of lines 3237-3247.
* `Λ̂_t` (`\regcluster{}{t}`, centred at `0`) is the harmonic ball family of Theorem 5.5 / Theorem 1.1: as in
  `Draft/Section1.lean`, statements are made for any random family `Λ` which is almost surely a harmonic ball family at
  `0` (`IsHarmonicBallFamily`, correction [C7]); given the uniqueness of Theorem 1.1 this is the printed statement.
* `B_δ(A) = A + B_δ` (line 331) is `thickening δ A`; `dist(A, {0})` is `infDist 0 A`; `D_h(A, B)` is `setDist`
  (eq:set-dist, line 461); `D_h(u, v; W)` is `internalMetric` (eq:internal-metric, line 427); the LQG metric ball
  `𝓑_u(0; D_h)` is `lqgMetricBall D 0 u` (line 3157). Distances are compared in `[0, ∞]` through `ENNReal.ofReal`
  (the values of `D_h` are non-negative a.s.).

## The pinch-point configuration (Section 11.3)

The sets `U ⋐ T`, `Q' ⋐ Q` (and `V`, `W`, `δ₀` in the proof of Lemma 11.12) are fixed once for the whole subsection
"as shown in Figure fig:pinch-point"; the keyhole shape of `T` is not formalized beyond the printed requirements
(`IsPinchPointConfiguration`). Lemma 11.14 is deterministic and its proof (lines 3170-3196) uses only those
requirements: it is stated for every configuration. Lemmas 11.12, 11.13 and 11.15-11.17 depend on the shape: they are
stated as `∃ configuration, requirements ∧ claim`, with the configuration chosen before every other parameter (it is
fixed independently of `γ`, `α₀`, `M`).

## Corrections and readings

* [C11] (proposed, E13): Lemma 11.12 (line 3137) "`P[G̃_1(0)] > 0`" is read "for each `M > 0`, `P[Ĝ_1(0; M)] > 0`".
* Lemma 11.6 (line 2764): `t` is unbound and no probability qualifier is printed; read "almost surely, for all
  `t > 0`" (`Λ̂_t` is defined on an event of probability one).
* Propositions 11.2, 11.11: "for Lebesgue-a.e. `t`" is `∀ᵐ t, 0 < t → ...` (the family is indexed by `t > 0`).
* Proposition 11.11 ("not an LQG-metric ball"): any centre and any radius, as in Theorem 1.2 (`Draft/Section1.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-! ## Objects of Section 11 -/

/-- The event `G̃_r(z) = G̃_r(z; M, 𝒬)` (eq:mu-h-wild, line 2793):
`μ_h(𝔸_{r,2r}(z) ∩ 𝒬(z)) ≥ M × SG_{3r,6r}(z)`. `G̃_n(z) := G̃_{2^{-n}}(z)` (line 2799). -/
def coneMassEvent (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ) (z : ℂ) : Prop :=
  ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) ≤ μ (annulus z r (2 * r) ∩ coneAt Q z)

/-- The pinch-point event `Ĝ_r(z) = Ĝ_r(z; M)` (eq:pinch-point-event, line 3124) for the configuration
`U, T, Q', Q`:
`D_h(Q'_r(z), ∂Q_r(z)) > sup_{x ∈ ∂B_{5r}(z)} D_h(z, x)`,
`D_h(z, ∂B_{5r}(z)) > sup_{x, y ∈ T_r(z)} D_h(x, y)` and `μ_h(U_r(z)) > M × SG_{3r,6r}(z)`.
`A_r(z) = rA + z` is `rescaledSet A r z`; `Ĝ_n(z) := Ĝ_{2^{-n}}(z)` (line 3133). -/
def pinchPointEvent (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ) : Prop :=
  (⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x)) <
      ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) ∧
    (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z, ENNReal.ofReal (D x y)) <
      ENNReal.ofReal (setDist D {z} (sphere z (5 * r))) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) < μ (rescaledSet U r z)

/-- `diam^δ_h(A) := sup_{x, y ∈ A} D_h(x, y; B_δ(A))` (line 3252), the diameter of `A` for the internal metric of
its `δ`-neighbourhood. -/
noncomputable def internalDiam (D : ℂ → ℂ → ℝ) (δ : ℝ) (A : Set ℂ) : ℝ≥0∞ :=
  ⨆ x ∈ A, ⨆ y ∈ A, internalMetric D (thickening δ A) x y

/-- The event `Ẽ₁` (eq:first-event, line 3257):
`D_h(Q', ∂Q) > sup_{x ∈ ∂B_5} D_h(0, x; (B_{2δ₀}(Q ∪ W))ᶜ)` and
`D_h(0, ∂B_{δ₀}) > diam^{δ₀}_h(T \ B_{3δ₀}(W))`. -/
def pinchFirstEvent (D : ℂ → ℂ → ℝ) (W T Q' Q : Set ℂ) (δ₀ : ℝ) : Prop :=
  (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (thickening (2 * δ₀) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) ∧
    internalDiam D δ₀ (T \ thickening (3 * δ₀) W) < ENNReal.ofReal (setDist D {0} (sphere 0 δ₀))

/-- The event `Ẽ₂ = Ẽ₂(M)` (eq:second-event, line 3264):
`D_h(∂B_{δ₀}, ∂B_{2δ₀}) > diam^{δ₀}_h(V)` and `μ_h(U) > M × SG_{3,6}(0)`. -/
def pinchSecondEvent (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U V : Set ℂ) (δ₀ M : ℝ) : Prop :=
  internalDiam D δ₀ V < ENNReal.ofReal (setDist D (sphere 0 δ₀) (sphere 0 (2 * δ₀))) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 < μ U

/-- The event `Ẽ₃` (eq:third-event, line 3271): `D_h(∂B_{2δ₀}, ∂B_{3δ₀}) > diam^{δ₀}_h(B_{3δ₀}(W) \ V)`. -/
def pinchThirdEvent (D : ℂ → ℂ → ℝ) (V W : Set ℂ) (δ₀ : ℝ) : Prop :=
  internalDiam D δ₀ (thickening (3 * δ₀) W \ V) <
    ENNReal.ofReal (setDist D (sphere 0 (2 * δ₀)) (sphere 0 (3 * δ₀)))

/-- The sets `T, U, V, W, Q', Q` and the scale `δ₀` of the proof of Lemma 11.12 (lines 3237-3247): a pinch-point
configuration `U, T, Q', Q` (`IsPinchPointConfiguration`, line 3100) together with concentric Euclidean balls
`U ⋐ V ⋐ W ⋐ T` contained in `𝔸_{1,2}` (line 3238) and `δ₀ ∈ (0, 1/100)` with (eq:metric-delta0-choice, line 3241)
`B_{10δ₀}(T) ⋐ 𝔸_{1,6}`, `B_{10δ₀}(U) ⋐ V`, `B_{10δ₀}(V) ⋐ W`, `B_{10δ₀}(W) ⋐ 𝔸_{1,2}`, `B_{10δ₀}(Q') ⋐ Q` and
`B_{10δ₀}(Q) ⋐ 𝔸_{4,5} \ B_{10δ₀}(T)`. -/
structure IsPinchPointProofConfiguration (U V W T Q' Q : Set ℂ) (δ₀ : ℝ) : Prop
    extends IsPinchPointConfiguration U T Q' Q where
  concentric : ∃ (c : ℂ) (ρU ρV ρW : ℝ), U = ball c ρU ∧ V = ball c ρV ∧ W = ball c ρW
  closure_U_subset_V : closure U ⊆ V
  closure_V_subset_W : closure V ⊆ W
  closure_W_subset_T : closure W ⊆ T
  V_subset : V ⊆ annulus 0 1 2
  W_subset : W ⊆ annulus 0 1 2
  δ₀_mem : δ₀ ∈ Ioo (0 : ℝ) (1 / 100)
  thickening_T : closure (thickening (10 * δ₀) T) ⊆ annulus 0 1 6
  thickening_U : closure (thickening (10 * δ₀) U) ⊆ V
  thickening_V : closure (thickening (10 * δ₀) V) ⊆ W
  thickening_W : closure (thickening (10 * δ₀) W) ⊆ annulus 0 1 2
  thickening_Q' : closure (thickening (10 * δ₀) Q') ⊆ Q
  thickening_Q : closure (thickening (10 * δ₀) Q) ⊆ annulus 0 4 5 \ thickening (10 * δ₀) T

/-! ## Section 11.1: not Lipschitz -/

/-- Proposition 11.2 (prop:not-balls, line 2724). Almost surely, `Λ̂_t` is not a Lipschitz domain for Lebesgue-a.e.
`t > 0`. -/
def HarmonicBallNotLipschitzStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ¬ IsLipschitzDomain (Λ ω t)

/-- Lemma 11.5 (lemma:no-exterior-cone-condition, line 2754). Almost surely, for `μ_h`-a.e. `z ∈ ℂ`: if `t > 0` is
such that `z ∈ ∂Λ̂_t`, then `Λ̂_t` does not satisfy the cone condition (Definition 11.4) at `z`. -/
def NoConeConditionStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℝ, 0 < t → z ∈ frontier (Λ ω t) → ¬ SatisfiesConeCondition (Λ ω t) z

/-- Lemma 11.6 (lemma:harmonic-comparison-chain, line 2764). There is a universal constant `C > 0` such that the
following holds for each `r > 0` and `z ∈ ℂ` with `closure B_{10r}(z) ∌ 0`: if `𝔸_{4r,5r}(z) ∩ Λ̂_tᶜ ≠ ∅`, then
`μ_h(𝔸_{r,2r}(z) ∩ Λ̂_t) ≤ C × SG_{3r,6r}(z)` (eq:alternate-size-2-full, line 1140).

"Universal": `C` is chosen before all other parameters (in the proof it comes from Lemmas 6.8 and 6.10,
lemma:odometer-annuli, line 1389, lemma:odometer-bound-lqg-mass, line 1512, whose constants depend only on the aspect
ratios). The printed statement leaves `t` unbound and has no probability qualifier: it is read "almost surely, for all
`t > 0`". -/
def AnnulusMassBoundByHarmonicChainStmt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → ∀ z : ℂ, (0 : ℂ) ∉ closedBall z (10 * r) →
    (annulus z (4 * r) (5 * r) ∩ (Λ ω t)ᶜ).Nonempty →
    (μ ω) (annulus z r (2 * r) ∩ Λ ω t) ≤ ENNReal.ofReal C * annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r)

/-- Lemma 11.7 (lemma:mu_h-bad-and-harnack, line 2802). Let `𝒬` be a cone and `M > 0`. There is
`δ = δ(M) ∈ (0,1)` such that almost surely, for `μ_h`-a.e. `z ∈ ℂ`, for each large enough `N ∈ ℕ` (depending on `z`),
`#{n ∈ [N+1, 2N] ∩ ℤ : G̃_n(z; M, 𝒬) occurs} ≥ δ N` (eq:mu_h-bad, line 2804), with `G̃_n(z) = G̃_{2^{-n}}(z)`.
`δ` is deterministic: it is chosen after `γ, α₀, 𝒬, M` and before the probability space. -/
def ManyConeBadScalesStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ Q : Set ℂ, IsCone Q → ∀ M : ℝ, 0 < M →
  ∃ δ ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
    δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- Lemma 11.8 (lemma:positive-probability, line 2809). Let `𝒬` be a cone and `M > 0`. There is `p_M ∈ (0,1)` such
that `P[G̃_n(z; M, 𝒬)] ≥ p_M` for all `z` with `dist(𝔸_{2^{-n}, 6·2^{-n}}(z), {0}) > 2^{-n}/100` and all `n ≥ N(z)`
(eq:desired-claim, line 2811). The printed threshold `N(z)` depends on `z` and is otherwise unspecified: it is
existentially quantified after `z`. The lower bound is in inner-measure form (module docstring): the event contains a
measurable event of probability at least `p_M`. -/
def ConeBadEventProbabilityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ Q : Set ℂ, IsCone Q → ∀ M : ℝ, 0 < M →
  ∃ p ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ z : ℂ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (2 : ℝ)⁻¹ ^ n / 100 < infDist (0 : ℂ) (annulus z ((2 : ℝ)⁻¹ ^ n) (6 * (2 : ℝ)⁻¹ ^ n)) →
    ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z}, MeasurableSet A ∧ ENNReal.ofReal p ≤ P A

/-! ## Section 11.2: small diameter and large LQG mass -/

/-- Proposition 11.9 (prop:mass-diam-gen, line 2959). Let `U ⊆ V ⊆ W ⊆ ℂ` be bounded connected open sets with
`closure V ⊆ W` and `W ∩ ∂B_1(0) = ∅`. For each `C > ε > 0`, with positive probability (eq:mass-diam-gen, line 2962)
`sup_{u, v ∈ V} D_h(u, v; W) ≤ ε` and `μ_h(U) ≥ C` ("with positive probability" in inner-measure form, module
docstring). -/
def SmallMetricDiameterLargeMassStmt : Prop :=
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ U V W : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
    IsOpen V → IsConnected V → Bornology.IsBounded V →
    IsOpen W → IsConnected W → Bornology.IsBounded W →
    U ⊆ V → V ⊆ W → closure V ⊆ W → Disjoint W (sphere 0 1) →
  ∀ C ε : ℝ, 0 < ε → ε < C →
    ∃ A ⊆ {ω | (∀ u ∈ V, ∀ v ∈ V, internalMetric (D ω) W u v ≤ ENNReal.ofReal ε) ∧
      ENNReal.ofReal C ≤ μ ω U}, MeasurableSet A ∧ 0 < P A

/-- Lemma 11.10 (lemma:mass-diam, line 2979). Let `S₁ ⊆ S₂` be closed dyadic squares with `S₂ ∩ ∂B_1(0) = ∅`. For
each `C > ε > 0`, with positive probability (eq:mass-diam, line 2982) `sup_{u, v ∈ S₂} D_h(u, v; S₂) ≤ ε` and
`μ_h(S₁) ≥ C` ("with positive probability" in inner-measure form, module docstring). -/
def SmallMetricDiameterLargeMassSquareStmt : Prop :=
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ S₁ S₂ : Set ℂ, IsClosedDyadicSquare S₁ → IsClosedDyadicSquare S₂ → S₁ ⊆ S₂ → Disjoint S₂ (sphere 0 1) →
  ∀ C ε : ℝ, 0 < ε → ε < C →
    ∃ A ⊆ {ω | (∀ u ∈ S₂, ∀ v ∈ S₂, internalMetric (D ω) S₂ u v ≤ ENNReal.ofReal ε) ∧
      ENNReal.ofReal C ≤ μ ω S₁}, MeasurableSet A ∧ 0 < P A

/-! ## Section 11.3: not LQG metric balls -/

/-- Proposition 11.11 (prop:not-metric-balls, line 3091). Almost surely, `Λ̂_t` is not an LQG-metric ball for
Lebesgue-a.e. `t > 0`: `Λ̂_t ≠ 𝓑_s(w; D_h)` for every centre `w` and radius `s` (as in Theorem 1.2). -/
def HarmonicBallNotMetricBallStmt : Prop :=
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ (w : ℂ) (s : ℝ), Λ ω t ≠ lqgMetricBall (D ω) w s

/-- Lemma 11.12 (lemma:mu_h-pinch-positive-probability, line 3136), with the proposed correction [C11] (E13). In the
case `α₀ = 0`, for each `M > 0`, `P[Ĝ_1(0; M)] > 0`, for a pinch-point configuration `U, T, Q', Q` (chosen before all
other parameters; the keyhole shape of the figure is not formalized, see the module docstring).

The printed "`P[G̃_1(0)] > 0`" refers to the cone event of eq:mu-h-wild, whose parameters `M`, `𝒬` are not in scope;
the proof (lines 3291-3321) shows `Ẽ₁ ∩ Ẽ₂(M) ∩ Ẽ₃ ⊆ Ĝ_1(0; M)` and Lemma 11.13 uses `Ĝ`. "`P[Ĝ_1(0; M)] > 0`" is in
inner-measure form (module docstring). -/
def PinchEventPositiveProbabilityStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ ξ 0 hC D →
  ∀ M : ℝ, 0 < M →
    ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet A ∧ 0 < P A

/-- Lemma 11.13 (lemma:mu_h-pinch-bad, line 3144). For a pinch-point configuration `U, T, Q', Q` (chosen before all
other parameters): let `M > 0`; there is `δ ∈ (0,1)` such that almost surely, for `μ_h`-a.e. `z ∈ ℂ`, for each large
enough `N ∈ ℕ` (depending on `z`), `#{n ∈ [N+1, 2N] ∩ ℤ : Ĝ_n(z; M) occurs} ≥ δ N` (eq:mu_h-pinch-bad, line 3146),
with `Ĝ_n(z) = Ĝ_{2^{-n}}(z)`. `δ` is deterministic (chosen before the probability space). -/
def ManyPinchScalesStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ M : ℝ, 0 < M → ∃ δ ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
    δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- Lemma 11.14 (lemma:geometric-event-consequence, line 3160). Almost surely, for each `M > 0`, each `z ∈ ℂ` and
each `r > 0` with `0 ∉ B_{10r}(z)`: if `u > 0` is such that `Ĝ_r(z)` occurs and `z ∈ ∂𝓑_u(0; D_h)`, then
`Q'_r(z) ⊆ 𝓑_u(0; D_h)ᶜ` and `T_r(z) ⊆ 𝓑_u(0; D_h)`.

Stated for every pinch-point configuration: the proof (lines 3170-3196) uses only `Q' ⋐ Q ⊆ 𝔸_{4,5}`,
`∂B_5 ⊆ ∂T` and the length-space property of `D_h`. -/
def PinchEventMetricBallConsequenceStmt : Prop :=
  ∀ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ᵐ ω ∂P, ∀ M : ℝ, 0 < M → ∀ z : ℂ, ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ ball z (10 * r) →
    ∀ u : ℝ, 0 < u → pinchPointEvent (μ ω) (D ω) U T Q' Q M r z →
    z ∈ frontier (lqgMetricBall (D ω) 0 u) →
    rescaledSet Q' r z ⊆ (lqgMetricBall (D ω) 0 u)ᶜ ∧ rescaledSet T r z ⊆ lqgMetricBall (D ω) 0 u

/-- Lemma 11.15 (lemma:first-event-proof, line 3277). In the case `α₀ = 0` (proof of Lemma 11.12), for a
configuration `T, U, V, W, Q', Q, δ₀` of lines 3237-3247 (chosen before all other parameters): `P[Ẽ₁] > 0` (inner-measure
form, module docstring). -/
def PinchFirstEventPositiveStmt : Prop :=
  ∃ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ₀ ∧
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ 0 hC D →
  ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ₀}, MeasurableSet A ∧ 0 < P A

/-- Lemma 11.16 (lemma:second-event-proof, line 3281). In the case `α₀ = 0`, for a configuration
`T, U, V, W, Q', Q, δ₀` of lines 3237-3247 (chosen before all other parameters): for each `M > 0`,
`P[Ẽ₁ ∩ Ẽ₂(M)] > 0` (inner-measure form, module docstring). -/
def PinchSecondEventPositiveStmt : Prop :=
  ∃ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ₀ ∧
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ ξ 0 hC D →
  ∀ M : ℝ, 0 < M →
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ₀ ∧ pinchSecondEvent (μ ω) (D ω) U V δ₀ M},
      MeasurableSet A ∧ 0 < P A

/-- Lemma 11.17 (lemma:third-event-proof, line 3285). In the case `α₀ = 0`, for a configuration
`T, U, V, W, Q', Q, δ₀` of lines 3237-3247 (chosen before all other parameters): for each `M > 0`,
`P[Ẽ₁ ∩ Ẽ₂(M) ∩ Ẽ₃] > 0` (inner-measure form, module docstring). -/
def PinchThirdEventPositiveStmt : Prop :=
  ∃ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ₀ ∧
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ 0 hcirc μ → IsLQGMetricOfField P γ ξ 0 hC D →
  ∀ M : ℝ, 0 < M →
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ₀ ∧ pinchSecondEvent (μ ω) (D ω) U V δ₀ M ∧
      pinchThirdEvent (D ω) V W δ₀}, MeasurableSet A ∧ 0 < P A

end HarmonicBalls
