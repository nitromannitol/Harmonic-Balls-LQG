import HarmonicBalls.Proofs.Sec6.UniformSingularPrevalence
import HarmonicBalls.Proofs.Sec6.EightAdicSingularPrevalence

/-! # Simultaneous singular prevalence from zero-strength existence

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength existence
is a staged literature input pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

universe u

/-- A single zero-strength limit determines every existing singular limit
away from the origin, simultaneously for all singularity strengths. -/
theorem exists_ae_singular_limits_restrict_eq_weight_of_zero_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        μ.restrict {0}ᶜ = ((μ₀ ω).withDensity
          fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
  let := hG.isProbabilityMeasure
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  refine ⟨μ₀, hμ₀, ?_⟩
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ₀, hc0] with ω hm₀ hc₀ α μ hm
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => isLQGLimit_addCircleAverage hm₀ hc₀ f hf
  exact restrict_compl_zero_eq_withDensity hm hW

/-- A good-annulus subrange estimate for the whole-plane measure transfers
on one event to every existing singular LQG limit whose singularity strength lies in a fixed bounded interval. -/
theorem goodAnnuli_prevalence_all_singularities_of_zero_existence
    (hsub : GoodAnnuliSubRangeStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {b A : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hA : 0 ≤ A) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        c * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus μ r z a b}.ncard : ℝ)}) := by
  obtain ⟨c, hc, hsub⟩ := hsub
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ2 b hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  refine ⟨c, a / 4, hc, ⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
  refine ((hprev Ω P hC hcirc μ₀ hG hμ₀).inter_ae hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    exact hωW α μ hμ
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
bounded range of singularity strengths. -/
theorem veryGoodAnnuli_prevalence_all_singularities_of_zero_existence
    (hsub : VeryGoodAnnuliSubRangeStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {b A : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (hA : 0 ≤ A) :
    ∃ c C₃ a C₁m C₁p C₂m C₂p : ℝ,
      0 < c ∧ 0 < C₃ ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₁ : ℕ, 5 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ →
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        c * Real.logb 8 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus μ β ρ z N₀ a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}) := by
  obtain ⟨c, C₃, hc, hC₃, hsub⟩ := hsub
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, _, hprev⟩ :=
    hsub γ hγ hγ2 β hβ b hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  refine ⟨c, C₃, a / 4, C₁m / 4, 4 * C₁p, C₂m / 4, 4 * C₂p, hc, hC₃,
    ⟨by linarith [ha.1], by linarith [ha.2]⟩, by positivity, by positivity,
    by positivity, by positivity, max N₁ 5, le_max_of_le_right (by norm_num), ?_⟩
  intro N₀ hN₀
  have hN₀5 : 5 ≤ N₀ := (le_max_right _ _).trans hN₀
  refine ((hprev N₀ ((le_max_left _ _).trans hN₀) Ω P hC hcirc μ₀ hG hμ₀).inter_ae
    hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    exact hωW α μ hμ
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

/-- Eight-adic good-annulus prevalence holds simultaneously over every bounded
range of singularity strengths, with constants independent of the
range. -/
theorem eightAdic_goodAnnuli_all_singularities_of_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ A : ℝ, 0 ≤ A →
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus μ r z a b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hprev⟩ := eightAdic_goodAnnulus_prevalence_of_volumeGrowth hgrowth hγ hγ2 hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  refine ⟨a / 4, ⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
  intro A hA
  refine ((hprev Ω P hC hcirc μ₀ hG hμ₀).inter_ae hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    exact hωW α μ hμ
  refine ((logb_neg_half_le (by norm_num) (by norm_num : (0 : ℝ) < 1 / 32)
    hε0 hε.1.le).trans (hω z hz)).trans ?_
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
  · refine finite_of_geometric (q := (8 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε0 fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

/-- On one probability-one event, every existing singular limit has eight-adic
good-annulus prevalence for all sufficiently small inverse dyadic scales. -/
theorem ae_eventually_eightAdic_goodAnnuli_all_singularities_of_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ α : ℝ,
      ∀ᶠ k : ℕ in atTop, ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
        (1 / 32 : ℝ) * Real.logb 8 (((2 : ℝ)⁻¹ ^ k) ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  obtain ⟨a, ha, hp⟩ :=
    eightAdic_goodAnnuli_all_singularities_of_zero_existence hgrowth P γ hγ hγ2 hC hcirc hG hE0 hb
  refine ⟨a, ha, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
    (hp n (Nat.cast_nonneg n)).ae_eventually_dyadic)] with ω hω
  intro α
  obtain ⟨n, hn⟩ := exists_nat_gt |α|
  filter_upwards [hω n] with k hk
  exact hk α hn.le

end HarmonicBalls.Section6
