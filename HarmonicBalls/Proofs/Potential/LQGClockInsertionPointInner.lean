import HarmonicBalls.Proofs.Potential.LQGApproxNearInsertionPower
import HarmonicBalls.Proofs.Potential.BrownianOriginOccupationDensity

/-! # Inner clock occupation for Brownian motion started at the insertion point

A measure whose balls about the origin have power-law mass `C s^β` integrates the weight
`|z| ^ (-2 θ)`, for `2 θ < β`, over the ball of radius `ρ` with total at most a constant
times `ρ ^ (β - 2 θ)`. Combined with the occupation density of Brownian motion from the
origin and the power bound for the inserted circle-average approximations that holds
uniformly over the dyadic scales, the expected inner clock occupation from the origin
tends to zero with the inner radius, uniformly in the scale, for almost every field.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The weight `|z| ^ (-2 θ)` is dominated on the punctured ball by a geometric sum of ball
indicators. -/
theorem ofReal_norm_rpow_neg_le_tsum {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) {z : ℂ}
    (hz0 : z ≠ 0) (hzρ : ‖z‖ < ρ) :
    ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) ≤ ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) *
      ∑' j : ℕ, ENNReal.ofReal ((4 ^ θ) ^ j) *
        (ball (0 : ℂ) (ρ * 2⁻¹ ^ j)).indicator (fun _ => (1 : ℝ≥0∞)) z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hex : ∃ j : ℕ, ρ * 2⁻¹ ^ (j + 1) ≤ ‖z‖ := by
    obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (div_pos hn hρ) (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨n, ?_⟩
    have h1 : (2⁻¹ : ℝ) ^ (n + 1) ≤ 2⁻¹ ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
    have h2 : ρ * 2⁻¹ ^ (n + 1) ≤ ρ * 2⁻¹ ^ n := mul_le_mul_of_nonneg_left h1 hρ.le
    have h3 : ρ * 2⁻¹ ^ n < ‖z‖ := by
      rw [lt_div_iff₀ hρ] at hn'
      linarith
    linarith
  classical
  let j₀ := Nat.find hex
  have hj₀ : ρ * 2⁻¹ ^ (j₀ + 1) ≤ ‖z‖ := Nat.find_spec hex
  have hmem : z ∈ ball (0 : ℂ) (ρ * 2⁻¹ ^ j₀) := by
    rw [mem_ball, dist_zero_right]
    by_cases h0 : j₀ = 0
    · rw [h0, pow_zero, mul_one]
      exact hzρ
    · have hlt : ¬ (ρ * 2⁻¹ ^ (j₀ - 1 + 1) ≤ ‖z‖) := Nat.find_min hex (by omega)
      have he : j₀ - 1 + 1 = j₀ := by omega
      rw [he] at hlt
      exact lt_of_not_ge hlt
  have hpos : 0 < ρ * 2⁻¹ ^ (j₀ + 1) := by positivity
  calc ENNReal.ofReal ‖z‖ ^ (-(2 * θ))
      ≤ ENNReal.ofReal (ρ * 2⁻¹ ^ (j₀ + 1)) ^ (-(2 * θ)) :=
        by
          rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
          exact ENNReal.inv_le_inv.mpr
            (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hj₀) (by linarith))
    _ = ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) * ENNReal.ofReal ((4 ^ θ) ^ j₀) := by
        rw [ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h2 : ((2 : ℝ)⁻¹) ^ (-(2 * θ)) = 4 ^ θ := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv,
            Real.rpow_mul (by norm_num), Real.rpow_two]
          norm_num
        have hcomm : ((2 : ℝ)⁻¹ ^ (j₀ + 1)) ^ (-(2 * θ)) = ((2 : ℝ)⁻¹ ^ (-(2 * θ))) ^ (j₀ + 1) := by
          rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) (j₀ + 1),
            ← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ (-(2 * θ))) (j₀ + 1),
            ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
            mul_comm (((j₀ + 1 : ℕ)) : ℝ)]
        rw [Real.mul_rpow hρ.le (by positivity), hcomm, h2, pow_succ]
        ring
    _ ≤ ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) *
          ∑' j : ℕ, ENNReal.ofReal ((4 ^ θ) ^ j) *
            (ball (0 : ℂ) (ρ * 2⁻¹ ^ j)).indicator (fun _ => (1 : ℝ≥0∞)) z := by
        gcongr
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j₀)
        rw [Set.indicator_of_mem hmem, mul_one]

/-- **Power weight against a measure with power-law ball masses.** If balls about the origin
of radius `s ≤ r₀` have mass at most `C s ^ β` and the origin is not an atom, then for
`2 θ < β` and `ρ ≤ r₀` the weight `|z| ^ (-2 θ)` integrates over the ball of radius `ρ` to
at most `C 4^θ ρ^(β - 2θ) / (1 - 2^(-(β - 2θ)))`. -/
theorem lintegral_ball_norm_rpow_neg_le_of_ball_le {ν : Measure ℂ} {C β r₀ θ ρ : ℝ}
    (hC : 0 ≤ C) (hθ : 0 < θ) (hθβ : 2 * θ < β) (hρ : 0 < ρ) (hρr : ρ ≤ r₀)
    (hν : ∀ s : ℝ, 0 < s → s ≤ r₀ → ν (ball 0 s) ≤ ENNReal.ofReal (C * s ^ β))
    (h0 : ν {0} = 0) :
    ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) ∂ν ≤
      ENNReal.ofReal (C * 4 ^ θ * ρ ^ (β - 2 * θ) / (1 - 2 ^ (-(β - 2 * θ)))) := by
  set r : ℝ := 2 ^ (-(β - 2 * θ)) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hball : ∀ j : ℕ, ν (ball 0 (ρ * 2⁻¹ ^ j)) ≤
      ENNReal.ofReal (C * ρ ^ β * (2 ^ (-β)) ^ j) := by
    intro j
    have hs : 0 < ρ * 2⁻¹ ^ j := by positivity
    have hsr : ρ * 2⁻¹ ^ j ≤ r₀ :=
      (mul_le_of_le_one_right hρ.le (pow_le_one₀ (by norm_num) (by norm_num))).trans hρr
    refine (hν _ hs hsr).trans (le_of_eq ?_)
    congr 1
    have h2 : ((2 : ℝ)⁻¹) ^ β = 2 ^ (-β) := by
      rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
    have hcomm : ((2 : ℝ)⁻¹ ^ j) ^ β = ((2 : ℝ)⁻¹ ^ β) ^ j := by
      rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) j, ← Real.rpow_natCast ((2 : ℝ)⁻¹ ^ β) j,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm ((j : ℕ) : ℝ)]
    rw [Real.mul_rpow hρ.le (by positivity), hcomm, h2]
    ring
  have hae : ∀ᵐ z ∂ν, z ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  calc ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) ∂ν
      ≤ ∫⁻ z, ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) *
          ∑' j : ℕ, ENNReal.ofReal ((4 ^ θ) ^ j) *
            (ball (0 : ℂ) (ρ * 2⁻¹ ^ j)).indicator (fun _ => (1 : ℝ≥0∞)) z ∂ν := by
        rw [← lintegral_indicator measurableSet_ball]
        apply lintegral_mono_ae
        filter_upwards [hae] with z hz
        by_cases hzb : z ∈ ball (0 : ℂ) ρ
        · rw [Set.indicator_of_mem hzb]
          have hzρ : ‖z‖ < ρ := by simpa [mem_ball, dist_zero_right] using hzb
          exact ofReal_norm_rpow_neg_le_tsum hθ hρ hz hzρ
        · rw [Set.indicator_of_notMem hzb]
          exact zero_le
    _ = ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) *
          ∑' j : ℕ, ENNReal.ofReal ((4 ^ θ) ^ j) * ν (ball 0 (ρ * 2⁻¹ ^ j)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_tsum (f := fun (j : ℕ) (z : ℂ) => ENNReal.ofReal ((4 ^ θ) ^ j) *
          (ball (0 : ℂ) (ρ * 2⁻¹ ^ j)).indicator (fun _ => (1 : ℝ≥0∞)) z)
          fun j => ((measurable_const.indicator measurableSet_ball).const_mul _).aemeasurable]
        congr 1
        funext j
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator_const measurableSet_ball, one_mul]
    _ ≤ ENNReal.ofReal (4 ^ θ * ρ ^ (-(2 * θ))) *
          ∑' j : ℕ, ENNReal.ofReal (C * ρ ^ β) * ENNReal.ofReal r ^ j := by
        refine mul_le_mul_right (ENNReal.tsum_le_tsum fun j => ?_) _
        refine (mul_le_mul_right (hball j) _).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hr0,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h4 : (4 : ℝ) ^ θ * 2 ^ (-β) = r := by
          rw [hrdef, show (4 : ℝ) = 2 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
            ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 1
          ring
        rw [← h4, mul_pow]
        ring
    _ = ENNReal.ofReal (C * 4 ^ θ * ρ ^ (β - 2 * θ) / (1 - r)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hr0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_eq_mul_inv, show ρ ^ (β - 2 * θ) = ρ ^ (-(2 * θ)) * ρ ^ β by
          rw [← Real.rpow_add hρ]; ring_nf]
        ring

end HarmonicBalls
