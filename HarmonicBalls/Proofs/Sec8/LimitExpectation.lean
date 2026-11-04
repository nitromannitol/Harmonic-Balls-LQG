import HarmonicBalls.Proofs.Sec8.BlockFrequency

/-!
# Expectation of a limiting frequency

The dominated convergence step used after applying the ergodic theorem to
indicators of good annuli.
-/

open Filter MeasureTheory
open scoped Topology

namespace HarmonicBalls

/-- The expectation of an almost-sure limit of uniformly bounded functions
is the eventual common value of their expectations. -/
theorem integral_limit_eq_of_eventually_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (L : Ω → ℝ)
    (q C : ℝ) (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (L ω)))
    (hmean : ∀ᶠ n in atTop, ∫ ω, F n ω ∂P = q) :
    ∫ ω, L ω ∂P = q := by
  have ht := tendsto_integral_of_dominated_convergence (fun _ => C) hF
    (integrable_const C) hbound hlim
  have hq : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 q) :=
    tendsto_const_nhds.congr' (by filter_upwards [hmean] with n hn; exact hn.symm)
  exact tendsto_nhds_unique ht hq

/-- If the limiting frequency is almost surely constant, that constant is the
common expectation of the approximating frequencies. -/
theorem constant_limit_eq_of_eventually_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (L q C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 L))
    (hmean : ∀ᶠ n in atTop, ∫ ω, F n ω ∂P = q) : L = q := by
  simpa using integral_limit_eq_of_eventually_integral_eq P F (fun _ => L) q C
    hF hbound hlim hmean

open Classical in
/-- Once the prefix frequency has an almost-sure constant limit, its common
expectation gives the good-scale block estimate in Lemma 8.3. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_constant_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (F : ℕ → Ω → ℝ) (L q C ζ : ℝ)
    (hF_eq : ∀ N ω, F N ω =
      (∑ n ∈ Finset.Icc 1 N, if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0) /
          (N : ℝ))
    (hF : ∀ N, AEStronglyMeasurable (F N) P)
    (hbound : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => F N ω) atTop (𝓝 L))
    (hmean : ∀ᶠ N : ℕ in atTop, ∫ ω, F N ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  have hL : L = q := constant_limit_eq_of_eventually_integral_eq P F L q C
    hF hbound hlim hmean
  filter_upwards [hlim] with ω hω
  simp_rw [hF_eq] at hω
  exact eventually_veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m
    (hL ▸ hω) hq

end HarmonicBalls
