import HarmonicBalls.Proofs.Potential.BrownianStoppedLogPotentialTail

/-! # Sharp logarithmic tails of stopped Brownian occupation

The sharp ball occupation estimate gives a cubic logarithmic potential bound.
-/

open MeasureTheory MarkovProcess Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls

private theorem summable_dyadic_square :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k) := by
  have h0 := summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (1 / 4 : ℝ) < 1 by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (show ‖(1 / 4 : ℝ)‖ < 1 by norm_num)
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  ext k
  simp only [pow_one]
  ring

/-- A logarithmic ball-mass bound yields a cubic logarithmic potential bound. -/
theorem setLIntegral_ball_log_le_of_log_ball_bound {μ : Measure ℂ} {z : ℂ}
    {r C : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hC : 0 ≤ C)
    (hvol : ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤
      ENNReal.ofReal (C * (r * (1 / 2) ^ k) ^ 2 *
        (Real.log (1 / (r * (1 / 2) ^ k))) ^ 2)) :
    ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal (2 * C * (∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k) *
        r ^ 2 * (1 + Real.log (1 / r)) ^ 3) := by
  let L := Real.log (1 / r)
  let A := 1 + L
  let S := ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hc : 0 ≤ L + 1 + Real.log 2 := by linarith
  have hcA : L + 1 + Real.log 2 ≤ 2 * A := by dsimp [A]; linarith
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k) := summable_dyadic_square
  have hS : 0 ≤ S := tsum_nonneg (fun k => by positivity)
  have hvol' : ∀ k : ℕ, μ (ball z (r * (1 / 2) ^ k)) ≤
      ENNReal.ofReal (C * r ^ 2 * A ^ 2 * (((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k)) := by
    intro k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
    have hlog : Real.log (1 / (r * (1 / 2) ^ k)) = L + (k : ℝ) * Real.log 2 := by
      dsimp [L]
      rw [one_div, Real.log_inv, Real.log_mul hr.ne' hp.ne', Real.log_pow]
      have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hh, one_div, Real.log_inv]
      ring
    have hl0 : 0 ≤ L + (k : ℝ) * Real.log 2 := by positivity
    have hl : L + (k : ℝ) * Real.log 2 ≤ A * ((k : ℝ) + 1) := by
      dsimp [A]
      nlinarith [mul_nonneg hk hL, mul_nonneg hk (sub_nonneg.mpr hlog2le)]
    have hsquare : (L + (k : ℝ) * Real.log 2) ^ 2 ≤ (A * ((k : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ hl0 hl 2
    apply (hvol k).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hlog]
    have hpow : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc C * (r * (1 / 2) ^ k) ^ 2 * (L + (k : ℝ) * Real.log 2) ^ 2
        ≤ C * (r * (1 / 2) ^ k) ^ 2 * (A * ((k : ℝ) + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = _ := by rw [mul_pow, hpow, mul_pow]; ring
  calc ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
      ≤ ∫⁻ w in ball z r, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
          (fun _ => ENNReal.ofReal (L + 1 + Real.log 2)) w ∂μ := by
        exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2
          (Eventually.of_forall fun w hw => LatticeProb.LogKernel.ofReal_log_le_tsum_indicator hr (by linarith) hw))
    _ ≤ ∫⁻ w, ∑' k : ℕ, (ball z (r * (1 / 2) ^ k)).indicator
          (fun _ => ENNReal.ofReal (L + 1 + Real.log 2)) w ∂μ := setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ENNReal.ofReal (L + 1 + Real.log 2) * μ (ball z (r * (1 / 2) ^ k)) := by
        rw [lintegral_tsum fun k => (measurable_const.indicator measurableSet_ball).aemeasurable]
        exact tsum_congr fun k => lintegral_indicator_const measurableSet_ball _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((L + 1 + Real.log 2) * (C * r ^ 2 * A ^ 2) *
          (((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [show (L + 1 + Real.log 2) * (C * r ^ 2 * A ^ 2) *
          (((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k) =
          (L + 1 + Real.log 2) * (C * r ^ 2 * A ^ 2 *
          (((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k)) by ring, ENNReal.ofReal_mul hc]
        exact mul_le_mul_right (hvol' k) _
    _ = ENNReal.ofReal ((L + 1 + Real.log 2) * (C * r ^ 2 * A ^ 2) * S) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (hsum.mul_left _),
          tsum_mul_left]
    _ ≤ ENNReal.ofReal (2 * C * S * r ^ 2 * A ^ 3) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_nonneg hS (mul_nonneg hC (mul_nonneg (sq_nonneg r) (sq_nonneg A))),
          mul_nonneg (sub_nonneg.mpr hcA) (mul_nonneg hS (mul_nonneg hC (mul_nonneg (sq_nonneg r) (sq_nonneg A))))]

/-- For each start, one full-mass event gives a cubic logarithmic tail bound for every
bounded domain and every spatial center. -/
theorem planarBrownianMotion_stopped_uniform_sharp_log_potential_tail (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ D : Set ℂ, Bornology.IsBounded D →
      ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
          ∫⁻ w in ball z r, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1)
            ∂(stoppedBrownianOccupation D b) ≤
          ENNReal.ofReal (C * r ^ 2 * (1 + Real.log (1 / r)) ^ 3) := by
  filter_upwards [planarBrownianMotion_stopped_uniform_ball_occupation_log_all_domains x] with b hb D hD
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb D hD
  let S := ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ k
  have hS : 0 < S := by
    have h := summable_dyadic_square.sum_le_tsum (s := {0}) (fun k _ => by positivity)
    dsimp [S]
    simp only [Finset.sum_singleton, Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at h
    linarith
  refine ⟨2 * C * S, by positivity, min r₀ (1 / 2), lt_min hr₀ (by norm_num), ?_⟩
  intro z r hr hrsmall
  apply setLIntegral_ball_log_le_of_log_ball_bound hr (le_of_lt (lt_of_lt_of_le hrsmall (min_le_right _ _))) hC.le
  intro k
  apply hbound z _ (by positivity)
  have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact lt_of_le_of_lt (mul_le_of_le_one_right hr.le hp) (lt_of_lt_of_le hrsmall (min_le_left _ _))

end HarmonicBalls
