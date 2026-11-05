import HarmonicBalls.Proofs.Sec6.CompactUniformGoodAnnulus
import HarmonicBalls.Proofs.Sec6.ScaledGoodAnnulusIteration
import HarmonicBalls.Proofs.Sec6.ScaledCriterionThreeCount

/-! # Pathwise good-annulus thresholds at each scale

The fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Compact-parameter thresholds give a positive threshold at each dyadic
scale, uniformly over every centre and radius tested by criterion three.
The thresholds may depend on the scale and the measure. -/
theorem exists_scale_goodAnnulus_thresholds_of_compact
    (μ : Measure ℂ)
    (hcompact : ∀ (K : Set ℂ), IsCompact K → ∀ (R : Set ℝ), IsCompact R → R ⊆ Ioi 0 →
      ∀ b : ℝ, 0 < b → ∃ a : ℝ, 0 < a ∧
        ∀ z ∈ K, ∀ r ∈ R, IsGoodAnnulus μ r z a b)
    {s b : ℝ} (hs : 0 < s) (hb : 0 < b) (x : ℂ) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
      ∀ n z, z ∈ annulus x (s / 2) s →
        ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
          IsGoodAnnulus μ r z (a n) b := by
  classical
  have hex : ∀ n : ℕ, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ z ∈ closedBall x s,
        ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
          IsGoodAnnulus μ r z a b := by
    intro n
    have hRpos : Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ⊆ Ioi 0 := by
      intro r hr
      exact (mul_pos (dyadicScale_pos n) hs).trans_le hr.1
    obtain ⟨a, ha, hgood⟩ := hcompact (closedBall x s) (isCompact_closedBall x s) _
      isCompact_Icc hRpos b hb
    refine ⟨min a (1 / 2), ⟨lt_min ha (by norm_num), ?_⟩, ?_⟩
    · exact (min_le_right _ _).trans_lt (by norm_num)
    · intro z hz r hr
      exact isGoodAnnulus_mono_mass (hgood z hz r hr) (min_le_left _ _)
  choose a ha hgood using hex
  refine ⟨a, ha, ?_⟩
  intro n z hz r hr
  exact hgood n z (mem_closedBall.mpr (le_of_lt (mem_ball.mp hz.1))) r hr

/-- The geometric radius count is maximal at every centre and every phase
when all annuli in each dyadic radius window have the corresponding threshold. -/
theorem scale_goodAnnulus_count_eq_all_geometric
    {μ : Measure ℂ} {s b : ℝ} {x : ℂ} {a : ℕ → ℝ}
    (hgood : ∀ n z, z ∈ annulus x (s / 2) s →
      ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
        IsGoodAnnulus μ r z (a n) b)
    (n : ℕ) {z : ℂ} (hz : z ∈ annulus x (s / 2) s) :
    {r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ r z (a n) b} =
    {r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
      ∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k} := by
  ext r
  constructor
  · exact fun hr => ⟨hr.1, hr.2.1⟩
  · exact fun hr => ⟨hr.1, hr.2, hgood n z hz r hr.1⟩

/-- From level 48 onward, the seven-adic logarithmic window is long enough. -/
theorem sixteen_le_logb_dyadic_inverse {n : ℕ} (hn : 48 ≤ n) :
    16 ≤ Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num)
    (Real.rpow_pos_of_pos (dyadicScale_pos n) _), Real.rpow_neg_one]
  norm_num only [Real.rpow_natCast]
  have hpow : (7 : ℝ) ^ 16 ≤ (2 : ℝ) ^ n := by
    calc (7 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 48 := by norm_num
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at hpow
  simpa [dyadicScale, inv_pow] using hpow

/-- At every sufficiently fine scale, the maximal count satisfies the
criterion-three lower bound, simultaneously for all lattice phases. -/
theorem scale_goodAnnulus_criterion_count
    {μ : Measure ℂ} {s b : ℝ} {x : ℂ} {a : ℕ → ℝ}
    (hs : 0 < s)
    (hgood : ∀ n z, z ∈ annulus x (s / 2) s →
      ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
        IsGoodAnnulus μ r z (a n) b)
    {n : ℕ} (hn : 9 ≤ n)
    (hnlarge : 16 ≤ Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)))
    {z : ℂ} (hz : z ∈ annulus x (s / 2) s) :
    (1 / 16 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z (a n) b}.ncard : ℝ) := by
  classical
  have hε : 0 < dyadicScale n := dyadicScale_pos n
  have hε1 : dyadicScale n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (7 : ℝ))
      (by norm_num) hε 1 (by omega) (by simpa using hnlarge)
  have hnormgood : ∀ r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)),
      IsGoodAnnulus μ (s * r) z (a n) b := by
    intro r hr
    apply hgood n z hz (s * r)
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hr.1 hs.le]
    · have hr' : r ≤ Real.sqrt (dyadicScale n) := hr.2.trans (by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num))
      nlinarith [mul_le_mul_of_nonneg_left hr' hs.le]
  have hcount := geometric_scale_count_le (by norm_num : (0 : ℝ) < 7⁻¹)
    (by norm_num : (7 : ℝ)⁻¹ < 1) hε
    (fun t => IsGoodAnnulus μ (s * t) z (a n) b) n₀ 1 K (by omega) hrange
  have hall : ((Finset.range K).filter fun k =>
      IsGoodAnnulus μ (s * (7 : ℝ)⁻¹ ^ (n₀ + 1 * k)) z (a n) b) = Finset.range K := by
    apply Finset.filter_eq_self.mpr
    intro k hk
    exact hnormgood _ (hrange k hk)
  rw [hall, Finset.card_range] at hcount
  apply scaled_criterionThree_count_of_subrange (by norm_num) hs hn
  have hcast : (K : ℝ) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ (s * r) z (a n) b}.ncard : ℝ) := by
    exact_mod_cast hcount
  have hK' : Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) / 16 ≤ (K : ℝ) := by
    simpa using hK
  linarith

/-- Almost surely, a whole-plane LQG measure has scale-dependent thresholds
simultaneously over all positive outer radii, centres and phases. -/
theorem ae_exists_scale_goodAnnulus_thresholds_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (s b : ℝ), 0 < s → 0 < b → ∀ x : ℂ,
      ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
        ∀ n z, z ∈ annulus x (s / 2) s →
          ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
            IsGoodAnnulus (μ ω) r z (a n) b := by
  filter_upwards [ae_compact_goodAnnulus_thresholds_of_volumeGrowth hgrowth hγ hγ2 h hμ]
    with ω hω s b hs hb x
  exact exists_scale_goodAnnulus_thresholds_of_compact (μ ω) hω hs hb x

/-- The same common full-measure event works for every existing singular limit.
Zero-strength existence is a staged hypothesis pending source review. -/
theorem ae_all_singular_exists_scale_goodAnnulus_thresholds
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      ∀ (s b : ℝ), 0 < s → 0 < b → ∀ x : ℂ,
        ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
          ∀ n z, z ∈ annulus x (s / 2) s →
            ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
              IsGoodAnnulus μ r z (a n) b := by
  filter_upwards [ae_all_singular_compact_goodAnnulus_thresholds_of_zero_existence
    hgrowth P γ hγ hγ2 hC hcirc hG hE0] with ω hω α μ hlim s b hs hb x
  exact exists_scale_goodAnnulus_thresholds_of_compact μ (hω α μ hlim) hs hb x

/-- On one full-measure event, all existing singular limits have the
criterion-three count at every sufficiently fine scale and every centre, with
an almost-surely positive threshold that may vary with the scale. -/
theorem ae_all_singular_scale_criterion_counts
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      ∀ (s b : ℝ), 0 < s → 0 < b → ∀ x : ℂ,
        ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
          ∀ n, 48 ≤ n → ∀ z ∈ annulus x (s / 2) s,
            (1 / 16 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
                (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus μ r z (a n) b}.ncard : ℝ) := by
  filter_upwards [ae_all_singular_exists_scale_goodAnnulus_thresholds
    hgrowth P γ hγ hγ2 hC hcirc hG hE0] with ω hω α μ hlim s b hs hb x
  obtain ⟨a, ha, hgood⟩ := hω α μ hlim s b hs hb x
  refine ⟨a, ha, ?_⟩
  intro n hn z hz
  exact scale_goodAnnulus_criterion_count hs hgood (by omega)
    (sixteen_le_logb_dyadic_inverse hn) hz

end HarmonicBalls.Section6
