import HarmonicBalls.Proofs.Sec8.LimitExpectation

/-!
# Moments of good-scale frequencies

The average of bounded indicators is bounded by one, and its expectation is
the common one-scale expectation.
-/

open Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- The average over the first `N` scales is integrable. -/
theorem integrable_initialScaleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ∀ n, Integrable (X n) P) (N : ℕ) :
    Integrable (fun ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) P := by
  exact (integrable_finsetSum _ fun n _ => hX n).div_const _

/-- An average of numbers in `[0,1]` lies in `[0,1]`, including the
zero-scale convention. -/
theorem initialScaleAverage_mem_Icc (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) : (∑ n ∈ Icc 1 N, x n) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hs0 : 0 ≤ ∑ n ∈ Icc 1 N, x n := Finset.sum_nonneg fun n _ => (hx n).1
  have hs1 : (∑ n ∈ Icc 1 N, x n) ≤ N := by
    calc
      (∑ n ∈ Icc 1 N, x n) ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => (hx n).2
      _ = N := by simp [Nat.card_Icc]
  constructor
  · exact div_nonneg hs0 (Nat.cast_nonneg N)
  · by_cases hn : N = 0
    · simp [hn]
    · exact (div_le_one₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 hs1

/-- If all one-scale expectations agree, every nonempty initial average has
that expectation. -/
theorem integral_initialScaleAverage_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (q : ℝ)
    (hX : ∀ n, Integrable (X n) P) (hmean : ∀ n, ∫ ω, X n ω ∂P = q)
    {N : ℕ} (hN : 0 < N) :
    ∫ ω, (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ) ∂P = q := by
  rw [integral_div, integral_finsetSum _ (fun n _ => hX n)]
  simp only [hmean, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp

open Classical in
/-- For a measurable good-scale indicator process, the almost-sure constant
limit and its one-scale mean imply the good-scale block estimate. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_indicator_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (L q ζ : ℝ)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 L))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  have hXbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rw [hX]
    split_ifs <;> norm_num
  have hXi : ∀ n, Integrable (X n) P := by
    intro n
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm n).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hXbound n ω).1]
    exact (hXbound n ω).2
  apply ae_eventually_veryGoodComparableScaleCount_of_constant_limit P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m (fun N ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
    L q 1 ζ
  · intro N ω
    simp_rw [hX]
  · intro N
    exact (integrable_initialScaleAverage P X hXi N).aestronglyMeasurable
  · intro N
    filter_upwards with ω
    have hh := initialScaleAverage_mem_Icc (fun n => X n ω) (fun n => hXbound n ω) N
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2
  · exact hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact integral_initialScaleAverage_eq P X q hXi hmean (by omega)
  · exact hq

end HarmonicBalls
