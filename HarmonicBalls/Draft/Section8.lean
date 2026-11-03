import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Draft.Section11

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

`Draft/Section6.lean` does not exist yet; the good annulus event `E_r(z; a, b)`, the size `M_ρ(x₀)` and the very
good annulus event `Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` are defined here, as deterministic predicates of the measure
`μ` (the conditioning on `h` in eq:good-annulus-harmonic, line 1120, fixes `μ = μ_h`; the Brownian motion is
independent of `h`). `SG_ρ(x₀)` is `annulusGreenPotentialSup μ x₀ (ρ/4) (2ρ)` of `Draft/Section11.lean`. These
definitions are shared with Sections 6 and 11 and belong in a `Defs` file.

## Corrections and readings

* eq:good-annulus-harmonic (line 1120): as printed, "`𝓑^u` exits `𝔸_{3r,5r}(z)` before exiting `Y`" is impossible
  for `Y ⊆ 𝔸_{3r,5r}(z)`, so the printed event always holds. The intended event (slip at 1120, `GRAPH.md`; cf.
  lines 1090-1091) is `{τ_𝔸 ≤ τ_Y}`: the Brownian motion stays in `Y` until it exits the annulus.
* `β⁻` in `M_ρ` (eq:alternate-size, line 1129) is "the" lower exponent of Lemma 2.4, which allows any
  `β⁻ > (2+γ)²/2`. It is a parameter of the definitions and the statements hold for each such `β⁻` (Issue D10).
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

/-! ## Good and very good annuli (Section 6.2) -/

open MarkovProcess in
/-- The *good annulus* event `E_r(z) = E_r(z; a, b)` (eq:good-annulus-harmonic, lines 1115-1123), for the measure
`μ = μ_h`: for each Borel set `Y ⊆ 𝔸_{3r,5r}(z)` with `μ(Y) ≤ a μ(𝔸_{3r,5r}(z))` and each `u ∈ ∂B_{4r}(z)`, standard
planar Brownian motion `𝓑^u` stays in `Y` until it exits `𝔸_{3r,5r}(z)` (`τ_𝔸 ≤ τ_Y`, the corrected reading of
the slip at line 1120, see the module docstring) with probability at most `b`. The supremum over `u` of line 1120 is
the bound for every `u`; the probability is the outer measure, so no measurability of the event is presumed. -/
def IsGoodAnnulus (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ) : Prop :=
  ∀ Y : Set ℂ, MeasurableSet Y → Y ⊆ annulus z (3 * r) (5 * r) →
    μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
    ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤ ContinuousPath.exitTime Y p} ≤
        ENNReal.ofReal b

/-- The size `M_ρ(x₀)` (eq:alternate-size, line 1129):
`inf_{z ∈ 𝔸_{ρ/2,ρ}(x₀)} inf_{r ∈ (0, ρ/4)} μ(B_r(z)) / (r/ρ)^{β⁻}`, in `[0, ∞]`. -/
noncomputable def annulusBallMassSize (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ) : ℝ≥0∞ :=
  ⨅ z ∈ annulus x₀ (ρ / 2) ρ, ⨅ r ∈ Ioo 0 (ρ / 4), μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ βminus)

/-- The *very good annulus* event `Ē_ρ(x₀) = Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` (lines 1144-1157), for the measure
`μ = μ_h` and the exponent `β⁻` of `M_ρ`:
* (VG-i) `C₁⁻ ≤ M_ρ(x₀) / μ(𝔸_{ρ/4,2ρ}(x₀)) ≤ C₁⁺`;
* (VG-ii) `C₂⁻ ≤ SG_ρ(x₀) / μ(𝔸_{ρ/4,2ρ}(x₀)) ≤ C₂⁺`, with `SG_ρ(x₀)` of eq:alternate-size-2 (line 1134);
* (VG-iii) for each `ε ∈ {2^{-n}}_{n ≥ N₀}` and each `z ∈ (ερ/100) ℤ² ∩ 𝔸_{ρ/2,ρ}(x₀)` there are at least
  `C₃ log₇ ε^{-1/2}` radii `r ∈ [ερ, ε^{1/2} ρ] ∩ {ρ 7^{-k}}_{k ≥ 1}` for which `E_r(z; a, b)` occurs.

The ratios are taken in `[0, ∞]` (`x / 0 = ∞` for `x ≠ 0`, `0 / 0 = 0`), so (VG-i) and (VG-ii) fail when
`μ(𝔸_{ρ/4,2ρ}(x₀)) = 0` and the size is finite. The lattice `(ερ/100) ℤ²` is not centred at `x₀`, as printed
(Issue G21). -/
def IsVeryGoodAnnulus (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) : Prop :=
  annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
    annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) ∧
    ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
      (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) →
      C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)

/-! ## The annulus-ball comparison and the count of eq:mu_h-doubling -/

/-- The *annulus-ball comparison* event `G_n(z) = G_n(z; m)` (eq:annulus-ball-comparison, line 2140):
`μ(𝔸_{2^{-n-1},2^{-n}}(z)) ≥ m μ(B_{2^{-n}}(z))`. -/
def AnnulusBallComparison (μ : Measure ℂ) (n : ℕ) (z : ℂ) (m : ℝ) : Prop :=
  ENNReal.ofReal m * μ (ball z (dyadicScale n)) ≤ μ (annulus z (dyadicScale (n + 1)) (dyadicScale n))

/-- The count `#{n ∈ [N+1, 2N] ∩ ℤ : Ē_n(z) and G_n(z) occur}` of eq:mu_h-doubling (line 2155), where
`Ē_n(z) := Ē_{2^{-n}}(z)` (eq:very-good-annuli-event, line 2146) and `G_n(z) = G_n(z; m)`. -/
noncomputable def veryGoodComparableScaleCount (μ : Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (N : ℕ) : ℕ :=
  {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
    IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
    AnnulusBallComparison μ n z m}.ncard

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

/-! ## Sanity lemmas -/

/-- The annulus-ball comparison with `m = 0` always holds. -/
theorem annulusBallComparison_zero (μ : Measure ℂ) (n : ℕ) (z : ℂ) : AnnulusBallComparison μ n z 0 := by
  simp [AnnulusBallComparison]

/-- The good annulus event with `b ≥ 1` always holds (probabilities are at most one). -/
theorem isGoodAnnulus_of_one_le (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    IsGoodAnnulus μ r z a b := by
  unfold IsGoodAnnulus
  intro Y _ _ _ u _
  calc planarBrownianMotion u _ ≤ 1 := prob_le_one
    _ ≤ ENNReal.ofReal b := by simpa using ENNReal.ofReal_le_ofReal hb

/-- The count of eq:mu_h-doubling is at most `N`, the number of integers in `[N+1, 2N]`. -/
theorem veryGoodComparableScaleCount_le (μ : Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (N : ℕ) :
    veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N ≤ N := by
  calc veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N
      ≤ (Icc (N + 1) (2 * N)).ncard := Set.ncard_le_ncard (fun n hn => hn.1) (Set.finite_Icc _ _)
    _ = N := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Nat.card_Icc]; omega

end HarmonicBalls
