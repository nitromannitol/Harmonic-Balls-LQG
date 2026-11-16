import HarmonicBalls.Proofs.Potential.LQGApproxAllCenterConditional

/-!
# Power bounds for singular approximations

A compact-center power bound for ordinary approximations yields a power bound
for singular approximations on sufficiently small balls.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

private theorem logarithmic_comparison_mul_rpow {s a γ α κ R : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 ≤ a) :
    Real.exp (γ * (|α| *
      (|Real.log (s ^ a / 2)| + |Real.log (max 1 (R + 1))|))) * s ^ κ =
    Real.exp (γ * |α| * (Real.log 2 + |Real.log (max 1 (R + 1))|)) *
      s ^ (κ - a * (γ * |α|)) := by
  have hsa : s ^ a ≤ 1 := Real.rpow_le_one hs.le hs1 ha
  have hd : 0 < s ^ a / 2 := by positivity
  have hd1 : s ^ a / 2 ≤ 1 := by linarith
  have hl : Real.log (s ^ a / 2) ≤ 0 := Real.log_nonpos hd.le hd1
  rw [abs_of_nonpos hl, Real.log_div (Real.rpow_pos_of_pos hs a).ne' (by norm_num),
    Real.log_rpow hs, Real.rpow_def_of_pos hs κ,
    Real.rpow_def_of_pos hs (κ - a * (γ * |α|)), ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- An ordinary power bound yields a singular power bound when the insertion
neighborhood exponent is sufficiently small. -/
theorem ae_singular_approximant_all_center_power_of_ordinary_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ)
    (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ C₁ κ : ℝ, 0 < C₁ → a * (γ * |α|) < κ →
        (∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ,
          0 ≤ s → s ≤ 1 → lqgApprox γ (hcirc ω) (dyadicScale k) (ball z s) ≤
            ENNReal.ofReal (C₁ * s ^ κ)) →
        ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
          ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ → s ≤ 1 →
            s ≤ s ^ a / 2 →
            lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
              ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_singular_approximant_all_center_bound_of_ordinary_power
    hh hγ hγ2 hαQ hδ hr hρ hrρ R] with ω hω
  intro a ha ha1 C₁ κ hC₁ hκ hord
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hbound⟩ := hω a ha ha1
  let D := Real.exp (γ * |α| * (Real.log 2 + |Real.log (max 1 (R + 1))|))
  have hD : 0 < D := Real.exp_pos _
  refine ⟨C + D * C₁, min β (κ - a * (γ * |α|)), r₀,
    by positivity, lt_min hβ (sub_pos.mpr hκ), hr₀, ?_⟩
  intro k z hz s hs hsr hs1 hssep
  have hnear : C * s ^ β ≤ (C + D * C₁) * s ^ min β (κ - a * (γ * |α|)) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (min_le_left β (κ - a * (γ * |α|)))
    have hp0 : 0 ≤ s ^ min β (κ - a * (γ * |α|)) := (Real.rpow_pos_of_pos hs _).le
    nlinarith [mul_nonneg (mul_nonneg hD.le hC₁.le) hp0]
  have hfar : D * C₁ * s ^ (κ - a * (γ * |α|)) ≤
      (C + D * C₁) * s ^ min β (κ - a * (γ * |α|)) := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (min_le_right β (κ - a * (γ * |α|)))
    have hp0 : 0 ≤ s ^ min β (κ - a * (γ * |α|)) := (Real.rpow_pos_of_pos hs _).le
    have hp_mul := mul_le_mul_of_nonneg_left hp (mul_nonneg hD.le hC₁.le)
    nlinarith [mul_nonneg hC.le hp0]
  apply (hbound C₁ κ hord k z hz s hs hsr hs1 hssep).trans
  apply max_le
  · exact ENNReal.ofReal_le_ofReal hnear
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [show Real.exp (γ * (|α| *
      (|Real.log (s ^ a / 2)| + |Real.log (max 1 (R + 1))|))) * (C₁ * s ^ κ) =
      C₁ * (Real.exp (γ * (|α| *
        (|Real.log (s ^ a / 2)| + |Real.log (max 1 (R + 1))|))) * s ^ κ) by ring,
      logarithmic_comparison_mul_rpow hs hs1 ha.le]
    simpa only [D, mul_left_comm, mul_assoc] using hfar

private theorem small_radius_le_rpow_half {a s : ℝ} (ha : a < 1) (hs : 0 < s)
    (hsr : s ≤ (1 / 2 : ℝ) ^ (1 / (1 - a))) : s ≤ s ^ a / 2 := by
  have hp : 0 < 1 - a := sub_pos.mpr ha
  have hpow := Real.rpow_le_rpow hs.le hsr hp.le
  have hbound : s ^ (1 - a) ≤ (1 / 2 : ℝ) := by
    convert hpow using 1
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have he : 1 / (1 - a) * (1 - a) = 1 := div_mul_cancel₀ 1 hp.ne'
    rw [he, Real.rpow_one]
  rw [Real.rpow_sub hs, Real.rpow_one] at hbound
  have hsa : 0 < s ^ a := Real.rpow_pos_of_pos hs _
  exact (div_le_iff₀ hsa).mp hbound |>.trans_eq (by ring)

/-- The conditional compact-center power estimate holds on all sufficiently
small balls, without a radius-separation assumption. -/
theorem ae_singular_approximant_small_ball_power_of_ordinary_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ)
    (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a → a < 1 →
      ∀ C₁ κ : ℝ, 0 < C₁ → a * (γ * |α|) < κ →
        (∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ,
          0 ≤ s → s ≤ 1 → lqgApprox γ (hcirc ω) (dyadicScale k) (ball z s) ≤
            ENNReal.ofReal (C₁ * s ^ κ)) →
        ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
          ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
            lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
              ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_singular_approximant_all_center_power_of_ordinary_power
    hh hγ hγ2 hαQ hδ hr hρ hrρ R] with ω hω
  intro a ha ha1 C₁ κ hC₁ hκ hord
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hbound⟩ := hω a ha ha1.le C₁ κ hC₁ hκ hord
  let t : ℝ := (1 / 2 : ℝ) ^ (1 / (1 - a))
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C, β, min r₀ (min 1 t), hC, hβ, lt_min hr₀ (lt_min zero_lt_one ht), ?_⟩
  intro k z hz s hs hsr
  have hs0 : s ≤ r₀ := hsr.trans (min_le_left _ _)
  have hs1 : s ≤ 1 := hsr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hst : s ≤ t := hsr.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact hbound k z hz s hs hs0 hs1 (small_radius_le_rpow_half ha1 hs hst)

/-- A positive ordinary compact-center power bound implies a positive singular
compact-center power bound on a common event. -/
theorem ae_singular_approximant_small_ball_power_of_positive_ordinary_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ)
    (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ C₁ κ : ℝ, 0 < C₁ → 0 < κ →
      (∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ,
        0 ≤ s → s ≤ 1 → lqgApprox γ (hcirc ω) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (C₁ * s ^ κ)) →
      ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
        ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
          lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
            ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_singular_approximant_small_ball_power_of_ordinary_power
    hh hγ hγ2 hαQ hδ hr hρ hrρ R] with ω hω
  intro C₁ κ hC₁ hκ hord
  obtain ⟨b, hb, hbκ⟩ := exists_pos_mul_lt hκ (γ * |α|)
  let a : ℝ := min b (1 / 2)
  have ha : 0 < a := lt_min hb (by norm_num)
  have ha1 : a < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have haκ : a * (γ * |α|) < κ := by
    have hle := mul_le_mul_of_nonneg_left (min_le_left b (1 / 2))
      (mul_nonneg hγ.le (abs_nonneg α))
    exact lt_of_le_of_lt (by simpa only [mul_comm] using hle) hbκ
  exact hω a ha ha1 C₁ κ hC₁ haκ hord

end HarmonicBalls
