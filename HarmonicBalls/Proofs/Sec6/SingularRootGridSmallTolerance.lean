import HarmonicBalls.Proofs.Sec6.SingularMassDyadicSmallTolerance
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Singular-root and prevalence-grid counts

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- For almost every field and singular-mass-typical root, both the
prescribed prevalence-grid count and the root count hold eventually on
dyadic windows. The two counts use their own thresholds and scale windows. -/
theorem exists_ae_singular_root_and_grid_eventually_dyadic_counts_smallTolerance
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c a₁ a₂ : ℝ, 0 < c ∧ a₁ ∈ Ioo (0 : ℝ) 1 ∧ a₂ ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a₁ b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
            (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) (s i * r) z
              (a₂ / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b}.ncard : ℝ)) := by
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  obtain ⟨c, a₁, hc, ha₁, hgrid⟩ :=
    goodAnnuli_prevalence_all_singularities_of_zero_existence
      (goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth)
      P γ hγ hγ2 hC hcirc h hE₀ hb (abs_nonneg α)
  obtain ⟨a₂, ha₂, hroot⟩ :=
    exists_ae_singular_mass_eventually_dyadic_goodAnnuli_count_of_existence_smallTolerance
      hball hγ hγ2 hα h hμ hE₀ hb.1 β hβ s hs
  refine ⟨c, a₁, a₂, hc, ha₁, ha₂, ?_⟩
  filter_upwards [hgrid.ae_eventually_dyadic, hroot, hμ] with ω hg hr hlim
  filter_upwards [hr] with z hz
  refine ⟨?_, hz⟩
  filter_upwards [hg] with n hn
  exact hn α le_rfl (μ ω) hlim

/-- Lowering the mass threshold can only increase a finite seven-adic count. -/
theorem sevenAdic_goodAnnulus_count_mono
    (μ : Measure ℂ) (z : ℂ) (s lo hi a a' b : ℝ) (hlo : 0 < lo) (ha : a' ≤ a) :
    ({r : ℝ | r ∈ Icc lo hi ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ (s*r) z a b}.ncard : ℝ) ≤
    ({r : ℝ | r ∈ Icc lo hi ∧ (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ (s*r) z a' b}.ncard : ℝ) := by
  norm_cast
  apply Set.ncard_le_ncard ?_ ?_
  · intro r hr
    exact ⟨hr.1, hr.2.1, isGoodAnnulus_mono_mass hr.2.2 ha⟩
  · apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := lo)
      (by norm_num) (by norm_num) hlo
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa using hn⟩

/-- The prescribed grid and singular-mass-typical roots share one positive
mass threshold and the same avoidance tolerance, eventually along their
respective dyadic windows. -/
theorem exists_ae_singular_root_and_grid_common_threshold
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
            (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) (s i * r) z a b}.ncard : ℝ)) := by
  obtain ⟨c, a₁, a₂, hc, ha₁, ha₂, ht⟩ :=
    exists_ae_singular_root_and_grid_eventually_dyadic_counts_smallTolerance
      hball hγ hγ2 hα h hμ hE₀ hb β hβ s hs
  let K : ℝ := ((1001 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  let a : ℝ := min a₁ (a₂ / K)
  have ha : 0 < a := lt_min ha₁.1 (div_pos ha₂.1 hK)
  refine ⟨c, a, hc, ⟨ha, lt_of_le_of_lt (min_le_left _ _) ha₁.2⟩, ?_⟩
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with z hz
  constructor
  · filter_upwards [hz.1] with n hn y hy
    have hh := sevenAdic_goodAnnulus_count_mono (μ ω) y 1 (dyadicScale n)
      (Real.sqrt (dyadicScale n)) a₁ a b (dyadicScale_pos n) (min_le_left _ _)
    simp only [one_mul] at hh
    exact (hn y hy).trans hh
  · intro i
    filter_upwards [hz.2 i] with n hn
    have hmono := sevenAdic_goodAnnulus_count_mono (μ ω) z (s i) (dyadicScale n)
      ((dyadicScale n) ^ (3 / 4 : ℝ)) (a₂ / K) a b (dyadicScale_pos n) (min_le_right _ _)
    have hhi : (dyadicScale n) ^ (3 / 4 : ℝ) ≤ Real.sqrt (dyadicScale n) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_ge (dyadicScale_pos n)
      · unfold dyadicScale
        exact pow_le_one₀ (by norm_num) (by norm_num)
      · norm_num
    apply (hn.trans hmono).trans
    norm_cast
    apply Set.ncard_le_ncard ?_ ?_
    · intro r hr
      exact ⟨⟨hr.1.1, hr.1.2.trans hhi⟩, hr.2⟩
    · apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
        (by norm_num) (by norm_num) (dyadicScale_pos n)
      intro r hr
      obtain ⟨k, hk⟩ := hr.2.1
      exact ⟨hr.1.1, k, by simpa using hk⟩

end HarmonicBalls.Section6
