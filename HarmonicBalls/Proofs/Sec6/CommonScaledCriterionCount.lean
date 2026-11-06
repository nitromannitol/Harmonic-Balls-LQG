import HarmonicBalls.Proofs.Sec6.SingularMassCommonThreshold
import HarmonicBalls.Proofs.Sec6.ScaledCriterionThreeCount

/-! # Physical-radius counts shared by two centres

The underlying annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Scaling a common seven-adic subrange count preserves the common radii
and gives the physical window and positive indices of criterion three. -/
theorem scaled_common_criterionThree_count_of_subrange
    {μ : Measure ℂ} {a b c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    {n : ℕ} (hn : 9 ≤ n) {z w : ℂ}
    (h : c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ (s*r) z a b ∧ IsGoodAnnulus μ (s*r) w a b}.ncard : ℝ)) :
    c * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a b ∧ IsGoodAnnulus μ r w a b}.ncard : ℝ) := by
  let ε := dyadicScale n
  have hε : 0 < ε := dyadicScale_pos n
  have hε1 : ε ≤ 1 := by dsimp [ε, dyadicScale]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  let T : Set ℝ := {r | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
    (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
    IsGoodAnnulus μ (s*r) z a b ∧ IsGoodAnnulus μ (s*r) w a b}
  let U : Set ℝ := {r | r ∈ Icc (ε*s) (Real.sqrt ε*s) ∧
    (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
    IsGoodAnnulus μ r z a b ∧ IsGoodAnnulus μ r w a b}
  have hfin : U.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := s) (lo := ε*s)
      (by norm_num) (by norm_num) (mul_pos hε hs) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩
  have hinj : Function.Injective (fun r : ℝ => s*r) := by
    intro x y hxy
    exact mul_left_cancel₀ hs.ne' hxy
  have hsub : (fun r : ℝ => s*r) '' T ⊆ U := by
    rintro r ⟨t, ht, rfl⟩
    have ht_sqrt : t ≤ Real.sqrt ε := ht.1.2.trans (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num))
    obtain ⟨k, hk⟩ := ht.2.1
    have hk1 : 1 ≤ k := by
      by_contra hbad
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      have : Real.sqrt ε ≤ (1 / 20 : ℝ) := hsqrt
      linarith
    refine ⟨⟨?_, ?_⟩, ⟨k, hk1, by rw [hk]⟩, ht.2.2⟩
    · nlinarith [mul_le_mul_of_nonneg_left ht.1.1 hs.le]
    · nlinarith [mul_le_mul_of_nonneg_left ht_sqrt hs.le]
  have hcard : T.ncard ≤ U.ncard := by
    calc
      T.ncard = ((fun r : ℝ => s*r) '' T).ncard := hinj.injOn.ncard_image.symm
      _ ≤ U.ncard := Set.ncard_le_ncard hsub hfin
  exact ((logb_neg_half_le (by norm_num) hc hε hε1).trans h).trans (by exact_mod_cast hcard)

/-- The prescribed grid and a singular-mass-typical root have counts with
one threshold, while the root and its nearby fine-grid centre share the
physical radii and radius window appearing in criterion three. -/
theorem exists_ae_singular_mass_prescribed_grid_and_common_physical_radii
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ c₀ a δ : ℝ, 0 < c₀ ∧ a ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      ∃ c : ℕ → ℝ, (∀ i, 0 < c i) ∧
      ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω).restrict (ball 0 1),
        (∀ᶠ n : ℕ in atTop, ∀ y ∈ prevalenceGrid (dyadicScale n),
          c₀ * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)) ∧
              (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r y a b}.ncard : ℝ)) ∧
        (∀ i, ∀ᶠ n : ℕ in atTop,
          ∃ z ∈ prevalenceGrid (c i * dyadicScale n),
            dist w z < δ * (s i * dyadicScale n) ∧
            (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-(1 / 2 : ℝ))) ≤
              ({r : ℝ | r ∈ Icc (dyadicScale n * s i) (Real.sqrt (dyadicScale n) * s i) ∧
                (∃ k : ℕ, 1 ≤ k ∧ r = s i * (7 : ℝ)⁻¹ ^ k) ∧
                IsGoodAnnulus (μ ω) r z a b ∧
                IsGoodAnnulus (μ ω) r w a b}.ncard : ℝ)) := by
  obtain ⟨c₀, a, δ, hc₀, ha, hδ, c, hc, ht⟩ :=
    exists_ae_singular_mass_prescribed_grid_and_common_radii_threshold
      hball h hμ hE₀ hAff hCC hγ hγ2 hα hb β hβ s hs
  refine ⟨c₀, a, δ, hc₀, ha, hδ, c, hc, ?_⟩
  filter_upwards [ht] with ω hω
  filter_upwards [hω] with w hw
  refine ⟨hw.1, ?_⟩
  intro i
  filter_upwards [hw.2 i, eventually_ge_atTop 9] with n hn hn9
  obtain ⟨z, hz, hdist, hcount⟩ := hn
  exact ⟨z, hz, hdist, scaled_common_criterionThree_count_of_subrange
    (div_pos hβ.1 (by norm_num)) (hs i) hn9 hcount⟩

end HarmonicBalls.Section6
