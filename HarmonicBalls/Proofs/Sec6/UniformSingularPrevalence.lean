import HarmonicBalls.Proofs.Sec6.Prevalence
import HarmonicBalls.Proofs.Sec6.CanonicalSingularMeasures

/-! # Simultaneous prevalence for bounded singularities

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The cofinal existence
hypotheses below are staged literature inputs pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

universe u

/-- The localization scale can be chosen uniformly over bounded strengths. -/
theorem eventually_small_for_bounded_strengths (γ A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 ∧ ∀ α : ℝ, |α| ≤ A →
      |-(γ * α)| * (2 * ε ^ (1 / 4 : ℝ)) ≤ Real.log 2 := by
  filter_upwards [eventually_small (γ * A), self_mem_nhdsWithin] with ε hε hε0
  refine ⟨hε.1, ?_⟩
  intro α hα
  have hbound : |-(γ * α)| ≤ |γ * A| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hα (abs_nonneg γ)
  exact (mul_le_mul_of_nonneg_right hbound
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hε0.le _))).trans hε.2

/-- A good-annulus subrange estimate for the whole-plane measure transfers
on one event to every existing subcritical LQG limit whose singularity
strength lies in a fixed bounded interval. -/
theorem goodAnnuli_prevalence_simultaneous_bounded_singularities
    (hsub : GoodAnnuliSubRangeStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b A : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hA : 0 ≤ A) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A → α < lqgQ γ →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        c * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus μ r z a b}.ncard : ℝ)}) := by
  obtain ⟨c, hc, hsub⟩ := hsub
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ2 b hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  refine ⟨c, a / 4, hc, ⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
  refine ((hprev Ω P hC hcirc μ₀ hG hμ₀).inter_ae hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA hα μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    rw [hωW α hα μ hμ]
  refine ((logb_neg_half_le (by norm_num) hc hε0 hε.1.le).trans (hω z hz)).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨⟨hr.1.1, ?_⟩, hr.2.1, ?_⟩) ?_
  · calc r ≤ ε ^ (3 / 4 : ℝ) := hr.1.2
      _ ≤ Real.sqrt ε := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.1.le (by norm_num)
  · have hr0 : 0 < r := hε0.trans_le hr.1.1
    exact isGoodAnnulus_of_comparable
      (isComparableOn_grid hε0 hε.1 hexp hweight hz (by positivity) (by linarith [hr.1.2]))
      sdiff_subset hr.2.2
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε) (by norm_num) (by norm_num) hε0
      fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

/-- Very-good annulus prevalence also holds simultaneously over every
bounded range of subcritical singularity strengths. -/
theorem veryGoodAnnuli_prevalence_simultaneous_bounded_singularities
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b A : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hA : 0 ≤ A) :
    ∃ c C₃ a C₁m C₁p C₂m C₂p : ℝ,
      0 < c ∧ 0 < C₃ ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₁ : ℕ, 5 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ →
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A → α < lqgQ γ →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        c * Real.logb 8 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus μ β ρ z N₀ a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}) := by
  obtain ⟨c, C₃, hc, hC₃, hsub⟩ := hsub
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, _, hprev⟩ :=
    hsub γ hγ hγ2 β hβ b hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  refine ⟨c, C₃, a / 4, C₁m / 4, 4 * C₁p, C₂m / 4, 4 * C₂p, hc, hC₃,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, by positivity, by positivity,
    by positivity, by positivity, max N₁ 5, le_max_of_le_right (by norm_num), ?_⟩
  intro N₀ hN₀
  have hN₀5 : 5 ≤ N₀ := (le_max_right _ _).trans hN₀
  refine ((hprev N₀ ((le_max_left _ _).trans hN₀) Ω P hC hcirc μ₀ hG hμ₀).inter_ae
    hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA hα μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    rw [hωW α hα μ hμ]
  refine ((logb_neg_half_le (by norm_num) hc hε0 hε.1.le).trans (hω z hz)).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun ρ hρ => ⟨⟨hρ.1.1, ?_⟩, hρ.2.1, ?_⟩) ?_
  · calc ρ ≤ ε ^ (3 / 4 : ℝ) := hρ.1.2
      _ ≤ Real.sqrt ε := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.1.le (by norm_num)
  · have hρ0 : 0 < ρ := hε0.trans_le hρ.1.1
    exact isVeryGoodAnnulus_of_comparable
      (isComparableOn_grid hε0 hε.1 hexp hweight hz (by positivity) (by linarith [hρ.1.2]))
      hρ0 hN₀5 hρ.2.2
  · refine finite_of_geometric (q := (8 : ℝ)⁻¹) (A := 1) (lo := ε) (by norm_num) (by norm_num) hε0
      fun ρ hρ => ⟨hρ.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hρ.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

end HarmonicBalls.Section6
