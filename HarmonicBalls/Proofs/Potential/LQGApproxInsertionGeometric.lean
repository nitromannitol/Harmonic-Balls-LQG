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
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
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

end HarmonicBalls
