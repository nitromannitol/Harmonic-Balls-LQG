import HarmonicBalls.Proofs.Sec7.ContinuityAtScales
import HarmonicBalls.Proofs.Sec7.ContinuityReduction

/-!
# Continuity from eventually good dyadic scales

An eventually good sequence of volume and Harnack events supplies the
small-scale continuity estimate for all positive time increments.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise

/-- The deterministic assembly of the dyadic estimates used in Proposition 7.2. -/
theorem eventually_contained_of_good_dyadic_scales
    (μ : Measure ℂ) {A : Set ℂ} {B : ℝ → Set ℂ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hAne : A.Nonempty)
    (hAmeas : NullMeasurableSet A μ) (hAfin : μ A ≠ ⊤)
    (hcompact : closure A ⊆ ball 0 1)
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ᶠ n : ℕ in atTop,
      (∀ x ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal (((((2 : ℝ)⁻¹) ^ n) / 8) ^ β) ≤ μ (ball x ((((2 : ℝ)⁻¹) ^ n) / 8))) ∧
      (∀ w ∈ prevalenceGrid (((2 : ℝ)⁻¹) ^ n),
        ∃ ρ ∈ Icc (((2 : ℝ)⁻¹) ^ n) (Real.sqrt (((2 : ℝ)⁻¹) ^ n)), P ρ w))
    (hstep : ∀ T : ℝ, 0 < T → A ⊆ B T ∧ IsPreconnected (B T) ∧
      μ (B T) ≤ μ A + ENNReal.ofReal T)
    (hharnack : ∀ T : ℝ, 0 < T → ∀ w ρ, ρ ∈ Ioo (0 : ℝ) 1 → P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ A →
      μ (B T ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B T ∩ ball w (ρ / 2) = ∅) :
    ∀ᶠ T in 𝓝[>] (0 : ℝ),
      closure (B T) ⊆ A + ball 0 ((140 * α ^ (-(4 * β)⁻¹)) * T ^ (1 / (4 * β))) := by
  have hK : IsCompact (closure A) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hcompact)
  obtain ⟨d, hd, hdunit⟩ := hK.exists_cthickening_subset_open isOpen_ball hcompact
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hgood
  have hmin : 0 < min (1 / 8 : ℝ) ((d / 70) ^ 2) := by positivity
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one hmin (by norm_num : (2 : ℝ)⁻¹ < 1)
  let N := max N₁ N₂
  apply eventually_contained_of_dyadic_scales hα hβ N
  intro n hn T hT hbound
  let s : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hs : 0 < s := by dsimp [s]; positivity
  have hslt : s < min (1 / 8 : ℝ) ((d / 70) ^ 2) := by
    calc
      s ≤ ((2 : ℝ)⁻¹) ^ N₂ := pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (le_trans (le_max_right _ _) hn)
      _ < _ := hN₂
  have hs8 : s ≤ 1 / 8 := (hslt.trans_le (min_le_left _ _)).le
  have hsroot : s ≤ Real.sqrt s := Real.le_sqrt_self_iff.2 (by linarith)
  have hsqrtd : Real.sqrt s < d / 70 :=
    (Real.sqrt_lt hs.le (by positivity)).2 (hslt.trans_le (min_le_right _ _))
  have hsqrt1 : Real.sqrt s < 1 := (Real.sqrt_lt hs.le (by norm_num)).2 (by nlinarith)
  have hunit : thickening (70 * Real.sqrt s) A ⊆ ball 0 1 :=
    (thickening_subset_cthickening_of_le (by linarith : 70 * Real.sqrt s ≤ d) A).trans
      ((cthickening_subset_of_subset d subset_closure).trans hdunit)
  have hgoodn := hN₁ n (le_trans (le_max_left _ _) hn)
  have hstepT := hstep T hT
  have hmass : T ≤ α * (s / 8) ^ β :=
    hbound.trans (mul_le_mul_of_nonneg_left (rpow_double_le_div_eight_rpow hs hs8 hβ.le) hα.le)
  apply closure_subset_add_ball_of_increment_volume_and_harnack μ hs hsroot hα hAne
    hstepT.1 hstepT.2.1 hAmeas hAfin hstepT.2.2 hmass hunit hgoodn.1 P hgoodn.2
  intro w _ ρ hρ hP hdomain hsmall
  exact hharnack T hT w ρ ⟨lt_of_lt_of_le hs hρ.1, lt_of_le_of_lt hρ.2 hsqrt1⟩
    hP hdomain hsmall

end HarmonicBalls
