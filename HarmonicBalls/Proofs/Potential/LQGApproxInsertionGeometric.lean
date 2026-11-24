import HarmonicBalls.Proofs.Potential.LQGApproxSubscaleBallMass

/-!
# Geometric bounds for singular approximations near the insertion

A common geometric rate controls balls contained in shrinking neighborhoods
of the insertion, uniformly in the dyadic regularization scale.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- On one event, a geometric rate bounds all dyadic approximations on balls
contained in the stated insertion-centered neighborhoods. -/
theorem ae_singular_approximant_contained_ball_geometric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ A t : ℝ, 0 < A ∧ 0 < t ∧ t < 1 ∧ ∃ n J₀ : ℕ, 0 < n ∧
      ∀ m k : ℕ, ∀ z : ℂ, ∀ s : ℝ,
        ‖z‖ + s ≤ dyadicScale (n * m) → dyadicScale (n * m) ≤ r → J₀ ≤ m →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (A * t ^ m) := by
  filter_upwards [ae_singular_approximant_contained_ball_bound
    hh hγ hγ2 hαQ hδ hρ hrρ] with ω hω
  obtain ⟨C, hC, n, hn, J₀, hbound⟩ := hω
  let q : ℝ := Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))
  let u : ℝ := Real.exp (-(Real.log 2) * n)
  let t : ℝ := max u q
  let A : ℝ := max (Real.pi * Real.exp (γ * C))
    (Real.exp (γ * (|α| * Real.log 2)) / (1 - q))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    have : 0 < γ * (lqgQ γ - α) * Real.log 2 / 2 := by positivity
    linarith
  have hu : 0 < u := Real.exp_pos _
  have hu1 : u < 1 := by
    dsimp [u]
    rw [Real.exp_lt_one_iff]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  have ht : 0 < t := lt_of_lt_of_le hu (le_max_left _ _)
  have ht1 : t < 1 := max_lt hu1 hq1
  have hA : 0 < A := lt_of_lt_of_le (mul_pos Real.pi_pos (Real.exp_pos _)) (le_max_left _ _)
  refine ⟨A, t, hA, ht, ht1, n, J₀, hn, ?_⟩
  intro m k z s hzs hr hm
  have hb := hbound (n * m) k z s hzs hr (by simpa [hn.ne'] using hm)
  refine hb.trans (max_le ?_ ?_)
  · apply ENNReal.ofReal_le_ofReal
    have hexp : Real.exp (-(Real.log 2) * (n * m : ℕ)) = u ^ m := by
      dsimp [u]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hu.le (le_max_left _ _) _)
      (pow_nonneg hu.le _) hA.le
  · apply ENNReal.ofReal_le_ofReal
    change Real.exp (γ * (|α| * Real.log 2)) * (q ^ (n * m / n) / (1 - q)) ≤ A * t ^ m
    rw [Nat.mul_div_cancel_left m hn]
    have hmul := mul_le_mul (le_max_right (Real.pi * Real.exp (γ * C))
      (Real.exp (γ * (|α| * Real.log 2)) / (1 - q)))
      (pow_le_pow_left₀ hq.le (le_max_right u q) m) (pow_nonneg hq.le _) hA.le
    convert hmul using 1; ring


/-- The geometric bound can be written as a positive power of each enclosing
radius in the same sequence. -/
theorem ae_singular_approximant_contained_ball_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ A β : ℝ, 0 < A ∧ 0 < β ∧ ∃ n J₀ : ℕ, 0 < n ∧
      ∀ m k : ℕ, ∀ z : ℂ, ∀ s : ℝ,
        ‖z‖ + s ≤ dyadicScale (n * m) → dyadicScale (n * m) ≤ r → J₀ ≤ m →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (A * dyadicScale (n * m) ^ β) := by
  filter_upwards [ae_singular_approximant_contained_ball_geometric
    hh hγ hγ2 hαQ hδ hρ hrρ] with ω hω
  obtain ⟨A, t, hA, ht, ht1, n, J₀, hn, hbound⟩ := hω
  let β : ℝ := -Real.log t / (n * Real.log 2)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ : 0 < β := by
    dsimp [β]
    exact div_pos (neg_pos.mpr (Real.log_neg ht ht1)) (mul_pos hn' hlog)
  refine ⟨A, β, hA, hβ, n, J₀, hn, ?_⟩
  intro m k z s hzs hr hm
  have heq : dyadicScale (n * m) ^ β = t ^ m := by
    rw [Real.rpow_def_of_pos (by unfold dyadicScale; positivity)]
    unfold dyadicScale
    rw [Real.log_pow, Real.log_inv]
    have hcancel : -(Real.log 2) * (n : ℝ) * β = Real.log t := by
      dsimp [β]
      field_simp
    rw [Nat.cast_mul]
    rw [← Real.exp_log ht, ← Real.exp_nat_mul]
    congr 1
    nlinarith [hcancel]
  rw [heq]
  exact hbound m k z s hzs hr hm


/-- Near the insertion, the mass is bounded by a positive power of the ball
radius, uniformly over all dyadic regularization scales. -/
theorem ae_singular_approximant_near_origin_ball_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
      ∀ k : ℕ, ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ r₀ → ‖z‖ ≤ s →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_singular_approximant_contained_ball_power
    hh hγ hγ2 hαQ hδ hρ hrρ] with ω hω
  obtain ⟨A, β, hA, hβ, n, J₀, hn, hbound⟩ := hω
  let b : ℝ := (2⁻¹ : ℝ) ^ n
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by
    dsimp [b]
    exact pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
  let r₀ : ℝ := min (r * b) (b ^ J₀) / 2
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  refine ⟨A * (2 / b) ^ β, β, r₀, by positivity, hβ, hr₀, ?_⟩
  intro k z s hs hs₀ hz
  have hx : 0 < 2 * s := by positivity
  have hxrb : 2 * s ≤ r * b := by dsimp [r₀] at hs₀; linarith [min_le_left (r * b) (b ^ J₀)]
  have hxJ : 2 * s ≤ b ^ J₀ := by dsimp [r₀] at hs₀; linarith [min_le_right (r * b) (b ^ J₀)]
  have hx1 : 2 * s ≤ 1 := hxJ.trans (pow_le_one₀ hb.le hb1.le)
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near_of_lt_one hx hx1 hb hb1
  have hm : J₀ ≤ m := by
    by_contra h
    have hle : m + 1 ≤ J₀ := by omega
    have hp := pow_le_pow_of_le_one hb.le hb1.le hle
    linarith
  have hscale : dyadicScale (n * m) = b ^ m := by
    dsimp [dyadicScale, b]
    rw [pow_mul]
  have hscale_r : dyadicScale (n * m) ≤ r := by
    rw [hscale]
    rw [pow_succ] at hmlo
    nlinarith
  have hzs : ‖z‖ + s ≤ dyadicScale (n * m) := by rw [hscale]; linarith
  refine (hbound m k z s hzs hscale_r hm).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hscale_le : dyadicScale (n * m) ≤ (2 / b) * s := by
    rw [hscale]
    rw [pow_succ] at hmlo
    have hle : b ^ m ≤ (2 * s) / b := (le_div_iff₀ hb).2 (by nlinarith)
    convert hle using 1; ring
  have hp := Real.rpow_le_rpow (by rw [hscale]; positivity) hscale_le hβ.le
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / b) hs.le] at hp
  nlinarith [Real.rpow_nonneg hs.le β, Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / b) β]

end HarmonicBalls
