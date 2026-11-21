import HarmonicBalls.Proofs.Potential.LQGClockAnnularFineFractionalMoment
import HarmonicBalls.Proofs.Potential.BrownianOccupationReturnIteration

/-! # Occupation moments of small discs before exit

For a density supported on a closed disc of radius `r`, the moment of its Brownian
occupation before the exit from a domain inside a concentric disc of radius `R` is
controlled by one visit, lasting until the exit from the concentric disc of radius
`b`. The logarithmic return estimate contributes the factor
`(q (log R - log r) / (log b - log r)) ^ q`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- Starting outside the disc of radius `b`, the path reaches the closed disc of radius
`r` before leaving a domain inside the disc of radius `R` with at most the logarithmic
probability, also for starts outside the domain. -/
theorem planarBrownian_hit_closedBall_before_exitTime_le (c : ℂ) {r b R : ℝ}
    (hr : 0 < r) (hrb : r < b) (hbR : b < R) {D : Set ℂ} (hDR : D ⊆ ball c R)
    {y : ℂ} (hy : y ∉ ball c b) :
    planarBrownianMotion y {ω : ContinuousPath ℂ | ∃ s : ℝ≥0, ω s ∈ closedBall c r ∧
      (s : ℝ≥0∞) < ContinuousPath.exitTime D ω} ≤
      ENNReal.ofReal (Real.log R - Real.log b) / ENNReal.ofReal (Real.log R - Real.log r) := by
  have hby : b ≤ ‖y - c‖ := by
    rw [mem_ball, dist_eq_norm, not_lt] at hy
    exact hy
  by_cases hyR : ‖y - c‖ < R
  · refine le_trans (measure_mono ?_) (planarBrownian_hit_closedBall_before_exit_le c hr hrb hbR
      hby hyR)
    rintro ω ⟨s, hs, hlt⟩
    refine ⟨s, ?_, hlt.trans_le (ContinuousPath.exitTime_mono hDR ω)⟩
    rw [mem_closedBall, dist_eq_norm] at hs
    exact hs
  · have hyD : y ∉ D := fun h => hyR (by simpa [mem_ball, dist_eq_norm] using hDR h)
    have hnull : planarBrownianMotion y {ω : ContinuousPath ℂ | ∃ s : ℝ≥0,
        ω s ∈ closedBall c r ∧ (s : ℝ≥0∞) < ContinuousPath.exitTime D ω} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp (ae_planarBrownianMotion_eval_zero y))
      rintro ω ⟨s, _, hlt⟩ h0
      have h0' : ω 0 = y := h0
      have hle : ContinuousPath.exitTime D ω ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
        ContinuousPath.exitTime_le_of_notMem D ω 0 (by rw [h0']; exact hyD)
      exact absurd (hlt.trans_le hle) (by simp)
    rw [hnull]
    exact zero_le

/-- The return factor of the iteration is at most `(q / (1 - θ)) ^ q`. -/
theorem div_one_sub_ofReal_rpow_le {θ q : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hq : 1 ≤ q)
    (M : ℝ≥0∞) :
    M / (1 - ENNReal.ofReal θ ^ (1 / q)) ^ q ≤ M * ENNReal.ofReal ((q / (1 - θ)) ^ q) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq' : 0 ≤ 1 / q := one_div_nonneg.mpr hq0.le
  have hbern : θ ^ (1 / q) ≤ 1 + 1 / q * (θ - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := θ - 1) (by linarith) hq'
      (by rw [div_le_one hq0]; exact hq)
    simpa using h
  have hlow : (1 - θ) / q ≤ 1 - θ ^ (1 / q) := by
    have : (1 - θ) / q = 1 / q * (1 - θ) := by ring
    rw [this]
    linarith
  have hpos : 0 < (1 - θ) / q := div_pos (by linarith) hq0
  have hA : 0 < 1 - θ ^ (1 / q) := lt_of_lt_of_le hpos hlow
  have hθq : 0 ≤ θ ^ (1 / q) := Real.rpow_nonneg hθ0 _
  rw [ENNReal.ofReal_rpow_of_nonneg hθ0 hq', ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hθq, ENNReal.ofReal_rpow_of_nonneg hA.le hq0.le,
    div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hA q)]
  refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) M
  rw [← Real.inv_rpow hA.le]
  refine Real.rpow_le_rpow (inv_nonneg.mpr hA.le) ?_ hq0.le
  rw [inv_le_comm₀ hA (div_pos hq0 (by linarith)), inv_div]
  exact hlow

/-- **Disc return iteration.** A density supported on the closed disc of radius `r`
about `c` has occupation moments before the exit from a domain inside the disc of
radius `R` bounded by the moment of one visit, lasting until the exit from the disc of
radius `b`, times `(q (log R - log r) / (log b - log r)) ^ q`. -/
theorem lintegral_pathOccupationBefore_rpow_le_of_disc_return
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : Ω → ℂ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    {c : ℂ} {r b R : ℝ} (hr : 0 < r) (hrb : r < b) (hbR : b < R)
    {D : Set ℂ} (hD : IsOpen D) (hDR : D ⊆ ball c R)
    (hfQ : ∀ ω z, z ∉ closedBall c r → f ω z = 0) {q : ℝ} (hq : 1 ≤ q) {M : ℝ≥0∞}
    (hM : ∀ y ∈ closedBall c r, (∫⁻ ω, ∫⁻ ω', pathOccupationBefore (f ω)
      (min (ContinuousPath.exitTime (ball c b) ω') (ContinuousPath.exitTime D ω')) ω' ^ q
        ∂planarBrownianMotion y ∂P) ≤ M) (x : ℂ) :
    (∫⁻ ω, ∫⁻ ω', pathOccupationBefore (f ω) (ContinuousPath.exitTime D ω') ω' ^ q
      ∂planarBrownianMotion x ∂P) ≤
      M * ENNReal.ofReal ((q * (Real.log R - Real.log r) / (Real.log b - Real.log r)) ^ q) := by
  have hlr : Real.log r < Real.log b := Real.log_lt_log hr hrb
  have hlb : Real.log b < Real.log R := Real.log_lt_log (hr.trans hrb) hbR
  have hd : 0 < Real.log R - Real.log r := by linarith
  set θ : ℝ := (Real.log R - Real.log b) / (Real.log R - Real.log r) with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hd]
    linarith
  have hθE : ENNReal.ofReal (Real.log R - Real.log b) /
      ENNReal.ofReal (Real.log R - Real.log r) = ENNReal.ofReal θ := by
    rw [hθdef, ENNReal.ofReal_div_of_pos hd]
  have hiter := lintegral_pathOccupationBefore_rpow_le_of_return f hf isClosed_closedBall
    isOpen_ball hD hfQ hq (θ := ENNReal.ofReal θ) (ENNReal.ofReal_lt_one.mpr hθ1)
    (fun y hy => (planarBrownian_hit_closedBall_before_exitTime_le c hr hrb hbR hDR hy).trans
      (le_of_eq hθE)) hM x
  have h1 : 1 - θ = (Real.log b - Real.log r) / (Real.log R - Real.log r) := by
    rw [hθdef]
    field_simp
    ring
  have hq' : q / (1 - θ) = q * (Real.log R - Real.log r) / (Real.log b - Real.log r) := by
    rw [h1]
    field_simp
  rw [← hq']
  exact hiter.trans (div_one_sub_ofReal_rpow_le hθ0 hθ1 hq M)

end HarmonicBalls
