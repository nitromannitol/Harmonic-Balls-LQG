import HarmonicBalls.Proofs.Sec2.CircleAverageTail

/-!
# Circle averages at large radii

The variance of the whole-plane GFF circle average at radius `r ≥ 1` is
`log r`. The singularity of the logarithmic kernel on the diagonal is
ignored only inside the circle integral.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- The covariance of the whole-plane GFF circle average at the origin for
radii at least one. -/
theorem wholePlaneGFFCov_circle_zero_large {r : ℝ} (hr : 1 ≤ r) :
    wholePlaneGFFCov (.circle r 0) (.circle r 0) = Real.log r := by
  have hr0 : 0 < r := by linarith
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) 0 r) 0 r = Real.log r
  rw [Real.circleAverage_congr_sphere (f₂ := fun _ => Real.log r), Real.circleAverage_const]
  intro x hx
  have hx' : ‖x‖ = r := by simpa [abs_of_pos hr0] using hx
  have heq : Real.circleAverage (fun y => wholePlaneCov x y) 0 r =
      Real.circleAverage (fun y => 2 * Real.log r - Real.log ‖y - x‖) 0 r := by
    apply Real.circleAverage_congr_codiscreteWithin _ hr0.ne'
    filter_upwards [self_mem_codiscreteWithin (sphere (0 : ℂ) |r|),
      compl_singleton_mem_codiscreteWithin x] with y hy hyx
    have hy' : ‖y‖ = r := by simpa [abs_of_pos hr0] using hy
    have hne : y ≠ x := by simpa using hyx
    have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm)
    rw [wholePlaneCov, hx', hy', max_eq_left hr, Real.log_div (by positivity) hnorm,
      Real.log_mul hr0.ne' hr0.ne', norm_sub_rev]
    ring
  change Real.circleAverage (fun y => wholePlaneCov x y) 0 r = Real.log r
  rw [heq]
  change Real.circleAverage ((fun _ : ℂ => 2 * Real.log r) - (fun y => Real.log ‖y - x‖)) 0 r = _
  rw [Real.circleAverage_sub (circleIntegrable_const _ _ _)
    (circleIntegrable_log_norm_sub_const r), Real.circleAverage_const]
  have hlog := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := 0) (a := x) hr0.ne'
  rw [zero_sub, norm_neg, hx', inv_mul_cancel₀ hr0.ne', Real.posLog_one, add_zero] at hlog
  rw [hlog]
  ring

/-- Circle averages at reciprocal radii at least one have the same law. -/
theorem IsWholePlaneGFF.identDistrib_circleAverage_inv
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 1 ≤ r) :
    IdentDistrib (fun ω => hcirc ω r 0) (fun ω => hcirc ω r⁻¹ 0) P P := by
  have hr0 : 0 < r := by linarith
  have hi : 0 < r⁻¹ := inv_pos.mpr hr0
  have hi1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have hG := hh.hasGaussianLaw_circle hr0 0
  have hGi := hh.hasGaussianLaw_circle hi 0
  have hvar : Var[fun ω => hcirc ω r 0; P] = Real.log r := by
    rw [← covariance_self hG.aemeasurable]
    exact (hh.covariance_eq (.circle r 0) (.circle r 0) hr0 hr0).trans
      (wholePlaneGFFCov_circle_zero_large hr)
  have hvari : Var[fun ω => hcirc ω r⁻¹ 0; P] = Real.log r := by
    rw [← covariance_self hGi.aemeasurable]
    have hcov := (hh.covariance_eq (.circle r⁻¹ 0) (.circle r⁻¹ 0) hi hi).trans
      (wholePlaneGFFCov_circle_zero hi hi1)
    change cov[fun ω => hcirc ω r⁻¹ 0, fun ω => hcirc ω r⁻¹ 0; P] = _ at hcov
    simpa only [Real.log_inv, neg_neg] using hcov
  refine ⟨hG.aemeasurable, hGi.aemeasurable, ?_⟩
  have hm : ∫ ω, hcirc ω r 0 ∂P = 0 := hh.integral_eq_zero (.circle r 0) hr0
  have hmi : ∫ ω, hcirc ω r⁻¹ 0 ∂P = 0 := hh.integral_eq_zero (.circle r⁻¹ 0) hi
  rw [hG.map_eq_gaussianReal, hGi.map_eq_gaussianReal, hm, hmi, hvar, hvari]

/-- Gaussian tail bound at large dyadic radii, transferred from the existing
small-radius estimate. -/
theorem IsWholePlaneGFF.largeCircleAverage_dyadic_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    P {ω | L ≤ |hcirc ω ((2 : ℝ) ^ n) 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * (((n : ℝ) + 1) * Real.log 2)))) := by
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have heq := (hh.identDistrib_circleAverage_inv hr).measure_mem_eq
    (measurableSet_le measurable_const measurable_id.abs : MeasurableSet {x : ℝ | L ≤ |x|})
  have htail := circleAverageDyadicTailStep_holds Ω P hC hcirc hh n L hL
  change P {ω | L ≤ |hcirc ω ((2 : ℝ) ^ n) 0|} =
    P {ω | L ≤ |hcirc ω (((2 : ℝ) ^ n)⁻¹) 0|} at heq
  rw [heq]
  simpa only [dyadicScale, inv_pow] using htail

/-- Along large dyadic radii, the circle average grows sublinearly in the
scale index, in the one-sided eventual form needed for positive drift. -/
theorem IsWholePlaneGFF.ae_eventually_largeCircleAverage_abs_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      |hcirc ω ((2 : ℝ) ^ n) 0| < δ * ((n : ℝ) + 1) := by
  let q : ℝ := Real.exp (-(δ ^ 2) / (2 * Real.log 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hδ)) (by positivity)
  let E : ℕ → Set Ω := fun n => {ω | δ * ((n : ℝ) + 1) ≤ |hcirc ω ((2 : ℝ) ^ n) 0|}
  have hbound : ∀ n, P (E n) ≤ ENNReal.ofReal (2 * q) * ENNReal.ofReal q ^ n := by
    intro n
    have ht := hh.largeCircleAverage_dyadic_tail n (L := δ * ((n : ℝ) + 1)) (by positivity)
    have hexp : Real.exp (-((δ * ((n : ℝ) + 1)) ^ 2) /
        (2 * (((n : ℝ) + 1) * Real.log 2))) = q * q ^ n := by
      dsimp [q]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      field_simp
      ring
    dsimp [E]
    calc
      P {ω | δ * ((n : ℝ) + 1) ≤ |hcirc ω ((2 : ℝ) ^ n) 0|} ≤
          ENNReal.ofReal (2 * Real.exp (-((δ * ((n : ℝ) + 1)) ^ 2) /
            (2 * (((n : ℝ) + 1) * Real.log 2)))) := ht
      _ = ENNReal.ofReal (2 * q) * ENNReal.ofReal q ^ n := by
        rw [hexp, ← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq0.le]
  have hsum : (∑' n, P (E n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  exact lt_of_not_ge hn

/-- The scale factors in the proof of Theorem 5.5 diverge along large
dyadic radii. The logarithmic singularity changes the drift from `Q` to
`Q - α₀`, which is strictly positive under the paper's hypothesis. -/
theorem IsWholePlaneGFF.ae_dyadic_scaleFactor_tendsto_atTop
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α₀ : ℝ} (hγ : 0 < γ) (hα : α₀ < lqgQ γ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      Real.exp (γ * (lqgQ γ * Real.log ((2 : ℝ) ^ n) +
        fieldCircleAverage α₀ (hcirc ω) ((2 : ℝ) ^ n) 0))) atTop atTop := by
  let b : ℝ := (lqgQ γ - α₀) * Real.log 2
  have hb : 0 < b := mul_pos (sub_pos.mpr hα) (Real.log_pos (by norm_num))
  filter_upwards [hh.ae_eventually_largeCircleAverage_abs_lt (half_pos hb)] with ω hω
  apply Real.tendsto_exp_atTop.comp
  have hlinear : Tendsto (fun n : ℕ => γ * (b / 2 * (n : ℝ) - b / 2)) atTop atTop := by
    exact (((tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hb)).atTop_add
      tendsto_const_nhds).const_mul_atTop hγ)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [hω] with n hn
  have hn0 : 0 < (2 : ℝ) ^ n := by positivity
  rw [fieldCircleAverage_eq α₀ (hcirc ω) hn0, norm_zero, max_eq_left hn0.le,
    Real.log_pow]
  have habs : -((b / 2) * ((n : ℝ) + 1)) < hcirc ω ((2 : ℝ) ^ n) 0 :=
    (abs_lt.mp hn).1
  dsimp [b] at habs ⊢
  nlinarith [mul_pos hγ (sub_pos.mpr hα), Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end HarmonicBalls
