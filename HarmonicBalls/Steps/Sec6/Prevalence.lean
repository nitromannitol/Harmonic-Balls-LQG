import HarmonicBalls.Draft.Section6

/-!
# Section 6 steps: prevalence of good and very good annuli at `α₀ = 0` on the sub-range `[ε, ε^{3/4}]`

The printed proofs of Lemmas 6.3 (lines 1278-1290 of paper/lqg_harmonic_ball-corrected.tex) and 6.6 (lines
1370-1385) give constants depending on `α₀`, since they apply Lemmas 6.4 and 6.7 at every scale, whose constants
genuinely depend on `α₀`. The printed
`α₀`-uniform statements follow by localization: the deterministic steps
S-Flat and S-Transfer are proved in `HarmonicBalls/Proofs/Sec6/Localization.lean`, and the `α₀`-uniform Lemmas 6.3,
6.6 are derived from the two steps below in `HarmonicBalls/Proofs/Sec6/Prevalence.lean`.

The steps are step S-SubRange: the statements of Lemmas 6.3 and 6.6 for the whole-plane GFF `h^ℂ` (`α₀ = 0`), with
the radii restricted to `[ε, ε^{3/4}]` and the count `c₀ log ε^{-1}` (about a quarter of the radii of the range).
Proof route (the paper's argument at `α₀ = 0` on `K = ⌊(1/4) log₇ ε^{-1}⌋`, resp. `⌊(1/8) log₈ ε^{-1}⌋`, radii):
* `E_r(z; a, b)`, resp. `Ē_ρ(x₀)`, is determined by `h^ℂ|_{𝔸_{3r,5r}(z)}`, resp. `h^ℂ|_{𝔸_{ρ/4,2ρ}(x₀)}`, modulo
  additive constant (Fact 2.1 II-III, lines 1278-1280, 1372-1377; measurability: GRAPH G16);
* Lemma 6.4 (resp. Lemma 6.7) at `α₀ = 0` and at the universal `p` of Lemma 6.5;
* Lemma 6.5 (GM20b Lemma 3.1) for annuli centred at `z` (translation invariance of `h^ℂ` modulo constants,
  eq:gff-scaling), with a universal exponent `α` large enough to beat the union bound over the `O(ε^{-2})` grid
  points (lines 1282-1291). For very good annuli the radii `8^{-n}` violate the spacing hypothesis of Lemma 6.5
  (GRAPH G17); every other radius (`64^{-n}`) satisfies it, which halves the count.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

open Section6

universe u

/-- Step S-SubRange for good annuli (Lemma 6.3 at `α₀ = 0` on `[ε, ε^{3/4}]`; AlphaUniformity.md §6.1). There is a
universal `c₀ > 0` such that for `b ∈ (0,1)` there is `a = a(b, γ) ∈ (0,1)` with: for the γ-LQG measure `μ₀` of the
whole-plane GFF `h^ℂ`, with polynomially high probability as `ε → 0`, each `z ∈ (B_{1+ε} \ B_{10√ε}) ∩ (ε/100) ℤ²`
has at least `c₀ log₇ ε^{-1}` radii `r ∈ [ε, ε^{3/4}] ∩ {7^{-n}}_{n ∈ ℕ}` for which `E_r(z; a, b)` occurs. -/
def GoodAnnuliSubRangeStep : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ₀ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ₀ →
  PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
    c₀ * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)}

/-- Step S-SubRange for very good annuli (Lemma 6.6 at `α₀ = 0` on `[ε, ε^{3/4}]`; AlphaUniformity.md §6.1, §6.3).
There are universal `c₀, C₃ > 0` such that for `β⁻ > (2+γ)²/2` and `b ∈ (0,1)` there are `a ∈ (0,1)`,
`C₁^±, C₂^± > 0` and `N₁ ≥ 1` with: for all `N₀ ≥ N₁` and the γ-LQG measure `μ₀` of the whole-plane GFF `h^ℂ`, with
polynomially high probability as `ε → 0`, each `x₀ ∈ (B_{1+ε} \ B_{10√ε}) ∩ (ε/100) ℤ²` has at least
`c₀ log₈ ε^{-1}` radii `ρ ∈ [ε, ε^{3/4}] ∩ {8^{-n}}_{n ∈ ℕ}` for which `Ē_ρ(x₀; N₀, a, b, C₁^±, C₂^±, C₃)` occurs. -/
def VeryGoodAnnuliSubRangeStep : Prop :=
  ∃ c₀ C₃ : ℝ, 0 < c₀ ∧ 0 < C₃ ∧
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∀ b ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
  ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ₀ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ₀ →
  PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
    c₀ * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
      ({ρ : ℝ | ρ ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
        IsVeryGoodAnnulus (μ₀ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}

end HarmonicBalls
