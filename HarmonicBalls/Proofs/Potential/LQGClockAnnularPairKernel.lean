import HarmonicBalls.Proofs.Potential.LQGClockAnnularSecondMoment

/-! # Extended-valued two-point bound for annular clock densities

The field expectation of a product of inserted densities is controlled by a
Riesz kernel, including on the diagonal.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The extended-valued two-point function on an annulus is bounded by a Riesz
kernel. The kernel is infinite on the spatial diagonal. -/
theorem lintegral_inserted_clock_density_mul_le_annulus
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) {z w : ℂ}
    (hzδ : δ ≤ ‖z‖) (hwδ : δ ≤ ‖w‖) (hz : ‖z‖ ≤ 1 / 2)
    (hw : ‖w‖ ≤ 1 / 2) :
    (∫⁻ ω, ENNReal.ofReal ((ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w))) ∂P) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2)) *
        (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2)) := by
  by_cases hzw : z = w
  · subst w
    have hγ2 : 0 < γ ^ 2 := sq_pos_of_ne_zero hγ
    have hC : ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    simp only [sub_self, norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_def,
      not_lt_of_ge (neg_nonpos.mpr hγ2.le), neg_ne_zero.mpr hγ2.ne', ite_false,
      ENNReal.mul_top hC, le_top]
  · have hr : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    have hnonneg : ∀ ω, 0 ≤ (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) := by
      intro ω
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_inserted_clock_density_mul hh hε γ α z w) (Filter.Eventually.of_forall hnonneg)]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 *
          (2 / ‖z - w‖) ^ (γ ^ 2)) := ENNReal.ofReal_le_ofReal
            (integral_inserted_clock_density_mul_le_annulus hh hε hεδ γ α hzδ hwδ hz hw hzw)
      _ = _ := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
          div_eq_mul_inv, ← Real.rpow_neg hr.le]
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_rpow_of_pos hr]

/-- The annular density product obeys the same Riesz bound at all spatial pairs. -/
theorem lintegral_annular_inserted_clock_density_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) (z w : ℂ) :
    (∫⁻ ω, ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) *
      ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) w) ∂P) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2)) *
        (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2)) := by
  by_cases hz : δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2
  · by_cases hw : δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hz, ite_eq_left hw]
      have heq : (∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
          ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) ∂P) =
        ∫⁻ ω, ENNReal.ofReal ((ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w))) ∂P := by
        apply lintegral_congr
        intro ω
        rw [← ENNReal.ofReal_mul (by positivity)]
      rw [heq]
      exact lintegral_inserted_clock_density_mul_le_annulus hh hε hεδ hγ α hz.1 hw.1 hz.2 hw.2
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hw, ENNReal.ofReal_zero, mul_zero, lintegral_zero]
      exact zero_le
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
    exact zero_le

end HarmonicBalls
