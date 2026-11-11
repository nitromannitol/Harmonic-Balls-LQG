import HarmonicBalls.FirstPass.S8d.RatioComparison

/-! # helper: the very-good annulus event under a density comparison

Completes the comparison of `IsVeryGoodAnnulus` (Defs/Annuli.lean:81) for the singular and the regular measure on the
annulus `D = 𝔸_{ρ/4,2ρ}(x₀)`, under `k₁ • lam|_D ≤ μ|_D ≤ k₂ • lam|_D` (`DensityComparison.lean`).

* `radii_set_finite`: the radii `ρ 7^{-k}` in a compact interval `[a, b]` with `a > 0` form a finite set.
* `isGoodAnnulus_transfer`: a good annulus for the regular measure is good for the singular one with threshold
  `a · k₁/k₂`, when the annulus `𝔸(z, 3r, 5r)` lies in `D`.
* `annulus_three_five_subset`: for `z ∈ 𝔸_{ρ/2,ρ}(x₀)` and `5r ≤ ρ/4`, `𝔸(z,3r,5r) ⊆ D`.
* `criterion3_count_transfer`: the count of good radii (criterion VG-iii) is monotone under the transfer.
* `isVeryGoodAnnulus_of_density`: the assembled comparison, with constants `C₁m k₁/k₂`, `C₁p k₂/k₁`, and likewise
  for `C₂`; `a` becomes `a k₁/k₂`, and `b`, `C₃`, `N₀` are unchanged.

The Brownian exit condition of `IsGoodAnnulus` does not involve the measure, and the only measure input is the
measure-level comparison on `D`. No new mathematics. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The radii `ρ 7^{-k}` (`k ≥ 1`) lying in a compact interval `[a, b]` with `a > 0` form a finite set. -/
theorem radii_set_finite (ρ a b : ℝ) (hρ : 0 < ρ) (ha : 0 < a) :
    {r : ℝ | r ∈ Icc a b ∧ ∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k}.Finite := by
  have key : ∀ k : ℕ, a ≤ ρ * (7 : ℝ)⁻¹ ^ k → k < ⌈ρ / a⌉₊ := by
    intro k hk
    have hpos : (0 : ℝ) < (7 : ℝ) ^ k := by positivity
    have hk7 : k < 7 ^ k := Nat.lt_pow_self (by norm_num)
    have hcast : (k : ℝ) < (7 : ℝ) ^ k := by exact_mod_cast hk7
    have h1 : (7 : ℝ) ^ k ≤ ρ / a := by
      rw [inv_pow] at hk
      rw [le_div_iff₀ ha]
      have h2 : ρ * ((7 : ℝ) ^ k)⁻¹ * (7 : ℝ) ^ k = ρ := by field_simp
      calc (7 : ℝ) ^ k * a = a * (7 : ℝ) ^ k := mul_comm _ _
        _ ≤ ρ * ((7 : ℝ) ^ k)⁻¹ * (7 : ℝ) ^ k := mul_le_mul_of_nonneg_right hk hpos.le
        _ = ρ := h2
    have h3 : (k : ℝ) < ⌈ρ / a⌉₊ := lt_of_lt_of_le (lt_of_lt_of_le hcast h1) (Nat.le_ceil _)
    exact_mod_cast h3
  apply (((Finset.range ⌈ρ / a⌉₊).image (fun k : ℕ => ρ * (7 : ℝ)⁻¹ ^ k)).finite_toSet).subset
  rintro r ⟨hr, k, _, rfl⟩
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨k, Finset.mem_range.2 (key k hr.1), rfl⟩)

/-- For `z ∈ 𝔸_{ρ/2,ρ}(x₀)` and `5r ≤ ρ/4`, the annulus `𝔸(z,3r,5r)` lies in `𝔸_{ρ/4,2ρ}(x₀)`. -/
theorem annulus_three_five_subset (x₀ z : ℂ) (ρ r : ℝ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) (hr : 5 * r ≤ ρ / 4) :
    annulus z (3 * r) (5 * r) ⊆ annulus x₀ (ρ / 4) (2 * ρ) := by
  intro y hy
  simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hz hy ⊢
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hy1, hy2⟩ := hy
  have t1 := dist_triangle y z x₀
  have t2 := dist_triangle z y x₀
  have t3 := dist_comm y z
  constructor <;> linarith

/-- A good annulus for the regular measure is a good annulus for the singular one, with threshold `a · k₁/k₂`, when
the annulus `𝔸(z,3r,5r)` lies in the annulus `D` on which the measures are compared. -/
theorem isGoodAnnulus_transfer (lam μ : Measure ℂ) (x₀ z : ℂ) (ρ r a b k₁ k₂ : ℝ)
    (ha : 0 ≤ a) (hk₁ : 0 < k₁) (hk₁₂ : k₁ ≤ k₂)
    (hlow : ENNReal.ofReal k₁ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hup : μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      ENNReal.ofReal k₂ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hA : annulus z (3 * r) (5 * r) ⊆ annulus x₀ (ρ / 4) (2 * ρ))
    (hgood : IsGoodAnnulus lam r z a b) :
    IsGoodAnnulus μ r z (a * (k₁ / k₂)) b := by
  unfold IsGoodAnnulus at hgood ⊢
  have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ hk₁₂
  have hAm : MeasurableSet (annulus z (3 * r) (5 * r)) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hc0 : ENNReal.ofReal k₁ ≠ 0 := (ENNReal.ofReal_pos.2 hk₁).ne'
  have hcT : ENNReal.ofReal k₁ ≠ ∞ := ENNReal.ofReal_ne_top
  have e : ENNReal.ofReal (a * (k₁ / k₂)) * ENNReal.ofReal k₂ = ENNReal.ofReal k₁ * ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_mul (mul_nonneg ha (div_nonneg hk₁.le hk₂.le)), ← ENNReal.ofReal_mul hk₁.le]
    congr 1
    field_simp
  intro Y hY hYA hYμ u hu
  have hYD : Y ⊆ annulus x₀ (ρ / 4) (2 * ρ) := hYA.trans hA
  have hlamY : lam Y ≤ ENNReal.ofReal a * lam (annulus z (3 * r) (5 * r)) := by
    have hbY := (set_bounds_of_restrict lam μ _ _ _ hlow hup Y hY hYD).1
    have hbA := (set_bounds_of_restrict lam μ _ _ _ hlow hup (annulus z (3 * r) (5 * r)) hAm hA).2
    refine (ENNReal.mul_le_mul_iff_right hc0 hcT).1 ?_
    calc ENNReal.ofReal k₁ * lam Y ≤ μ Y := hbY
      _ ≤ ENNReal.ofReal (a * (k₁ / k₂)) * μ (annulus z (3 * r) (5 * r)) := hYμ
      _ ≤ ENNReal.ofReal (a * (k₁ / k₂)) * (ENNReal.ofReal k₂ * lam (annulus z (3 * r) (5 * r))) :=
          mul_le_mul_of_nonneg_left hbA zero_le
      _ = ENNReal.ofReal k₁ * (ENNReal.ofReal a * lam (annulus z (3 * r) (5 * r))) := by
          rw [← mul_assoc, e, mul_assoc]
  exact hgood Y hY hYA hlamY u hu

/-- The count of good radii (criterion VG-iii of `IsVeryGoodAnnulus`) is monotone under the transfer: the regular
count is at most the singular count, for `n ≥ N₀ ≥ 9` and `z ∈ 𝔸_{ρ/2,ρ}(x₀)`. -/
theorem criterion3_count_transfer (lam μ : Measure ℂ) (x₀ z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀)
    (a b k₁ k₂ : ℝ) (ha : 0 ≤ a) (hk₁ : 0 < k₁) (hk₁₂ : k₁ ≤ k₂)
    (hlow : ENNReal.ofReal k₁ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hup : μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      ENNReal.ofReal k₂ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hz : z ∈ annulus x₀ (ρ / 2) ρ) (n : ℕ) (hn : N₀ ≤ n) :
    ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus lam r z a b}.ncard : ℝ) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z (a * (k₁ / k₂)) b}.ncard : ℝ) := by
  have hdn : dyadicScale n ≤ 1 / 512 := by
    unfold dyadicScale
    calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 9 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 512 := by norm_num
  have hdpos : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsq : Real.sqrt (dyadicScale n) ≤ 1 / 20 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hfin : ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z (a * (k₁ / k₂)) b}).Finite :=
    (radii_set_finite ρ (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) hρ (mul_pos hdpos hρ)).subset
      (fun r hr => ⟨hr.1, hr.2.1⟩)
  have hsub : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus lam r z a b} ⊆
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z (a * (k₁ / k₂)) b} := by
    intro r hr
    obtain ⟨hI, hk, hgood⟩ := hr
    refine ⟨hI, hk, ?_⟩
    have hr20 : 5 * r ≤ ρ / 4 := by
      have hle : r ≤ (1 / 20 : ℝ) * ρ :=
        le_trans hI.2 (by simpa using mul_le_mul_of_nonneg_right hsq hρ.le)
      linarith
    exact isGoodAnnulus_transfer lam μ x₀ z ρ r a b k₁ k₂ ha hk₁ hk₁₂ hlow hup
      (annulus_three_five_subset x₀ z ρ r hz hr20) hgood
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- The very-good annulus event is comparable under a density comparison on the annulus `D = 𝔸_{ρ/4,2ρ}(x₀)`:
the constants of criteria (VG-i), (VG-ii) are multiplied by `k₁/k₂` and `k₂/k₁`, and `a` by `k₁/k₂`. -/
theorem isVeryGoodAnnulus_of_density (lam μ : Measure ℂ) (x₀ : ℂ) (ρ βminus : ℝ) (hρ : 0 < ρ)
    (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (k₁ k₂ : ℝ) (hk₁ : 0 < k₁) (hk₁₂ : k₁ ≤ k₂)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 ≤ a) (hC₁m : 0 < C₁m) (hC₁p : 0 ≤ C₁p)
    (hC₂m : 0 < C₂m) (hC₂p : 0 ≤ C₂p)
    (hlow : ENNReal.ofReal k₁ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hup : μ.restrict (annulus x₀ (ρ / 4) (2 * ρ)) ≤
      ENNReal.ofReal k₂ • lam.restrict (annulus x₀ (ρ / 4) (2 * ρ)))
    (hlam : IsVeryGoodAnnulus lam βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃) :
    IsVeryGoodAnnulus μ βminus ρ x₀ N₀ (a * (k₁ / k₂)) b (C₁m * (k₁ / k₂)) (C₁p * (k₂ / k₁))
      (C₂m * (k₁ / k₂)) (C₂p * (k₂ / k₁)) C₃ := by
  obtain ⟨h1, h2, h3⟩ := hlam
  have hDm : MeasurableSet (annulus x₀ (ρ / 4) (2 * ρ)) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hbd : ∀ s : Set ℂ, MeasurableSet s → s ⊆ annulus x₀ (ρ / 4) (2 * ρ) →
      ENNReal.ofReal k₁ * lam s ≤ μ s ∧ μ s ≤ ENNReal.ofReal k₂ * lam s :=
    fun s hs hsD => set_bounds_of_restrict lam μ _ _ _ hlow hup s hs hsD
  have hD := hbd (annulus x₀ (ρ / 4) (2 * ρ)) hDm subset_rfl
  have hyl : ENNReal.ofReal k₁ * lam (annulus x₀ (ρ / 4) (2 * ρ)) ≤ μ (annulus x₀ (ρ / 4) (2 * ρ)) := hD.1
  have hyu : μ (annulus x₀ (ρ / 4) (2 * ρ)) ≤ ENNReal.ofReal k₂ * lam (annulus x₀ (ρ / 4) (2 * ρ)) := hD.2
  have hM := s8d_annulusBallMassSize_comparable lam μ x₀ ρ βminus (ENNReal.ofReal k₁) (ENNReal.ofReal k₂)
    (ENNReal.ofReal_pos.2 hk₁).ne' ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 (lt_of_lt_of_le hk₁ hk₁₂)).ne'
    ENNReal.ofReal_ne_top hbd
  have hG := s8d_annulusGreenPotentialSup_comparable lam μ x₀ (ρ / 4) (2 * ρ) (ENNReal.ofReal k₁)
    (ENNReal.ofReal k₂) hlow hup
  have hm1 := ratio_transfer _ _ _ _ k₁ k₂ C₁m C₁p hk₁ hk₁₂ hC₁m hC₁p h1 hM.1 hM.2 hyl hyu
  have hm2 := ratio_transfer _ _ _ _ k₁ k₂ C₂m C₂p hk₁ hk₁₂ hC₂m hC₂p h2 hG.1 hG.2 hyl hyu
  exact ⟨hm1, hm2, fun n hn z hz hlat => (h3 n hn z hz hlat).trans
    (criterion3_count_transfer lam μ x₀ z ρ hρ N₀ hN₀ a b k₁ k₂ ha hk₁ hk₁₂ hlow hup hz n hn)⟩


end HarmonicBalls
