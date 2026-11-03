import HarmonicBalls.Defs.Notation
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.Green

/-!
# Good and very good annuli, the sizes `M_ρ` and `SG_ρ`, the annulus-ball comparison

Annulus objects of Section 6.2 (lines 1105-1161 of the corrected draft) shared by Sections 6, 8 and 11, as deterministic
functions and predicates of a measure `μ` on `ℂ` (in the paper `μ = μ_h`; the conditioning on `h` in
eq:good-annulus-harmonic, line 1120, fixes `μ`, and the Brownian motion is independent of `h`):

* `IsGoodAnnulus μ r z a b`: the good annulus event `E_r(z; a, b)` (eq:good-annulus-harmonic, lines 1115-1123);
* `annulusBallMassSize μ β⁻ ρ x₀`: the size `M_ρ(x₀)` (eq:alternate-size, line 1129);
* `annulusGreenPotentialSup μ x₀ a b`: `SG_{a,b}(x₀)` (eq:alternate-size-2-full, line 1140), with
  `SG_ρ(x₀) = SG_{ρ/4,2ρ}(x₀)` (eq:alternate-size-2, line 1134); Section 11 uses `SG_{3r,6r}(z)`;
* `IsVeryGoodAnnulus μ β⁻ ρ x₀ N₀ a b C₁⁻ C₁⁺ C₂⁻ C₂⁺ C₃`: the very good annulus event
  `Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` (lines 1144-1157);
* `AnnulusBallComparison μ n z m`: the annulus-ball comparison event `G_n(z; m)` (eq:annulus-ball-comparison,
  line 2140), and `veryGoodComparableScaleCount`, the count of eq:mu_h-doubling (line 2155).

## Corrections and readings

* eq:good-annulus-harmonic (line 1120): as printed, "`𝓑^u` exits `𝔸_{3r,5r}(z)` before exiting `Y`" is impossible
  for `Y ⊆ 𝔸_{3r,5r}(z)`, so the printed event always holds. The intended event (slip at 1120, `GRAPH.md`; cf.
  lines 1090-1091) is `{τ_𝔸 ≤ τ_Y}`: the Brownian motion stays in `Y` until it exits the annulus.
* `β⁻` in `M_ρ` (eq:alternate-size, line 1129) is "the" lower exponent of Lemma 2.4, which allows any
  `β⁻ > (2+γ)²/2`. It is a parameter of the definitions (Issue D10).
* Green function on the diagonal: `SG` integrates the paper's value `G(x, x) = +∞` there (the junk value of
  `greenFunction` is not used); for `μ = μ_h`, which has no atoms, the diagonal does not contribute.
* The lattice `(ερ/100) ℤ²` of (VG-iii) is not centred at `x₀`, as printed (Issue G21).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-! ## Good annuli and the sizes `M_ρ`, `SG_ρ` -/

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

/-- `SG_{a,b}(x₀)` (eq:alternate-size-2-full, line 1140, with `a = s₁ρ`, `b = s₂ρ`): the supremum over
`x ∈ 𝔸_{a,b}(x₀)` of `∫_{𝔸_{a,b}(x₀)} G_{B_b(x₀)}(x, y) dμ(y)`, in `[0, ∞]`. The quantity `SG_ρ(x₀)` of
eq:alternate-size-2 (line 1134) is `annulusGreenPotentialSup μ x₀ (ρ/4) (2ρ)`; Section 11 uses `SG_{3r,6r}(z)`. On the
diagonal the integrand is the paper's value `G(x, x) = +∞` (the junk value of `greenFunction` is not used); for
`μ = μ_h`, which has no atoms, the diagonal does not contribute. -/
noncomputable def annulusGreenPotentialSup (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ annulus x₀ a b, ∫⁻ y in annulus x₀ a b,
    (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ

/-! ## Very good annuli -/

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

/-- `SG_{a,b}(x₀)` of the zero measure vanishes. -/
theorem annulusGreenPotentialSup_zero (x₀ : ℂ) (a b : ℝ) : annulusGreenPotentialSup 0 x₀ a b = 0 := by
  simp [annulusGreenPotentialSup]

/-- The count of eq:mu_h-doubling is at most `N`, the number of integers in `[N+1, 2N]`. -/
theorem veryGoodComparableScaleCount_le (μ : Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (N : ℕ) :
    veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N ≤ N := by
  calc veryGoodComparableScaleCount μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N
      ≤ (Icc (N + 1) (2 * N)).ncard := Set.ncard_le_ncard (fun n hn => hn.1) (Set.finite_Icc _ _)
    _ = N := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Nat.card_Icc]; omega

end HarmonicBalls
