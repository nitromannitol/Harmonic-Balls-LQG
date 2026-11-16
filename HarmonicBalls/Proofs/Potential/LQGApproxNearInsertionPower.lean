import HarmonicBalls.Proofs.Potential.LQGApproxInsertionGeometric

/-!
# Singular approximation masses near the insertion

A power bound holds uniformly over dyadic regularization scales for balls
whose centers approach the insertion at a prescribed power of their radius.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- One event supports positive-power bounds on neighborhoods of the insertion
whose radius is a prescribed power of the ball radius. -/
theorem ae_singular_approximant_near_origin_rpow_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
        ∀ k : ℕ, ∀ z : ℂ, ∀ s : ℝ, 0 < s → s ≤ r₀ → ‖z‖ ≤ s ^ a →
          lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
            ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_singular_approximant_near_origin_ball_power
    hh hγ hγ2 hαQ hδ hr hρ hrρ] with ω hω
  obtain ⟨C, β, R, hC, hβ, hR, hbound⟩ := hω
  intro a ha ha1
  let R' := min 1 ((R / 2) ^ a⁻¹)
  have hR' : 0 < R' := by dsimp [R']; positivity
  refine ⟨C * 2 ^ β, a * β, R', by positivity, by positivity, hR', ?_⟩
  intro k z s hs hsR hz
  have hs1 : s ≤ 1 := hsR.trans (min_le_left _ _)
  have hsa : s ≤ s ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hs hs1 ha1
  have hsR' : s ≤ (R / 2) ^ a⁻¹ := hsR.trans (min_le_right _ _)
  have hsaR : s ^ a ≤ R / 2 := by
    have h := Real.rpow_le_rpow hs.le hsR' ha.le
    simpa only [Real.rpow_inv_rpow (by positivity : 0 ≤ R / 2) ha.ne'] using h
  have hsub : ball z s ⊆ ball (0 : ℂ) (2 * s ^ a) := by
    intro w hw
    have hwz : ‖w - z‖ < s := by simpa only [mem_ball, dist_eq_norm] using hw
    have ht := norm_add_le (w - z) z
    rw [sub_add_cancel] at ht
    simp only [mem_ball, dist_zero_right]
    linarith
  calc
    lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)
          (ball 0 (2 * s ^ a)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * (2 * s ^ a) ^ β) :=
      hbound k 0 (2 * s ^ a) (by positivity) (by linarith) (by simp; positivity)
    _ = ENNReal.ofReal ((C * 2 ^ β) * s ^ (a * β)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hs.le a),
        ← Real.rpow_mul hs.le]
      congr 1
      ring

end HarmonicBalls
