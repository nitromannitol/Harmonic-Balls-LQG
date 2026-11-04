import HarmonicBalls.Proofs.Sec8.BirkhoffPort

/-! # Good-scale frequencies from almost-everywhere indicator versions

The pointwise ergodic theorem used through `BirkhoffPort` is from Leonardo
Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace HarmonicBalls

open Classical in
/-- The good-scale block estimate remains valid when the measurable indicators
agree with the actual good-scale indicators only almost everywhere. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_ae_indicator_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (L q ζ : ℝ)
    (hX : ∀ n, ∀ᵐ ω ∂P, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 L))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  have hbound : ∀ n, ∀ᵐ ω ∂P, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    filter_upwards [hX n] with ω hω
    rw [hω]
    split_ifs <;> norm_num
  have hXi : ∀ n, Integrable (X n) P := by
    intro n
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm n).aestronglyMeasurable
    filter_upwards [hbound n] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  let F : ℕ → Ω → ℝ := fun N ω => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)
  have hF : ∀ N, AEStronglyMeasurable (F N) P :=
    fun N => (integrable_initialScaleAverage P X hXi N).aestronglyMeasurable
  have hFb : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ 1 := by
    intro N
    filter_upwards [ae_all_iff.mpr hbound] with ω hω
    have hh := initialScaleAverage_mem_Icc (fun n => X n ω) hω N
    simpa only [F, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have hFm : ∀ᶠ N : ℕ in atTop, ∫ ω, F N ω ∂P = q := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact integral_initialScaleAverage_eq P X q hXi hmean (by omega)
  have hL : L = q := constant_limit_eq_of_eventually_integral_eq P F L q 1 hF hFb hlim hFm
  filter_upwards [hlim, ae_all_iff.mpr hX] with ω hω heq
  have hω' : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0) /
          (N : ℝ)) atTop (𝓝 q) := by
    simpa only [heq, hL] using hω
  exact eventually_veryGoodComparableScaleCount (μ ω) βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m hω' hq

open Classical in
/-- Stationary measurable versions with almost-surely local representatives
satisfy the good-scale block estimate under a trivial germ. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_ae_indicator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n, ∀ᵐ ω ∂P, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let L : Ω → ℝ := fun ω => limUnder atTop (fun N : ℕ =>
    (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
  have hLm : Measurable L := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro N
    exact ((Finset.measurable_sum _ fun n _ => hXm n).div_const _).stronglyMeasurable
  obtain ⟨c, hc⟩ := ae_eq_const_of_trivial_germ_of_ae_local P germ r hr hcofinal
    hrmono hgmono L hLm (ae_local_initialScaleFrequency P germ X hlocal) htrivial
  have hInt : Integrable (X 1) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hXm 1).aestronglyMeasurable
    filter_upwards [hX 1] with ω hω
    rw [hω]
    split_ifs <;> norm_num
  have hconv := ae_tendsto_initialScaleAverage_of_stationary P X
    (pointwiseBirkhoff_of_latticeProb _ _ _) hXm hInt hstat
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ)) atTop (𝓝 c) := by
    filter_upwards [hconv, hc] with ω ⟨d, hd⟩ hω
    have hdc : d = c := hd.limUnder_eq.symm.trans hω
    simpa only [hdc] using hd
  exact ae_eventually_veryGoodComparableScaleCount_of_ae_indicator_limit P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X c q ζ hX hXm hlim hmean hq

end HarmonicBalls
