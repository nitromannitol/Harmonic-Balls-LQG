import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation

/-! # Dilation of the outer odometer comparison -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A unit-disk odometer-to-Green-potential estimate transfers to the
corresponding dilated disk with the same constant. -/
theorem annulus_odometer_bound_of_scaled_unit_bound
    {μ : Measure ℂ} {k c t : ℝ} {p z : ℂ} {a b A B : ℝ} {C : ℝ≥0∞}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hA : annulus z a b ⊆ ball (0 : ℂ) 1 \ {p})
    (hunit : (⨆ x ∈ annulus z a b, odometerExt
        (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) p (c * t) x) ≤
      C * annulusGreenPotentialSup
        (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) z A B) :
    (⨆ y ∈ annulus (k • z) (k * a) (k * b),
        ENNReal.ofReal (odometer μ k (k • p) t y)) ≤
      C * annulusGreenPotentialSup μ (k • z) (k * A) (k * B) := by
  rw [iSup_odometerExt_annulus_comp_real_smul hk hc ht hA,
    annulusGreenPotentialSup_comp_real_smul_measure μ hk] at hunit
  rw [mul_left_comm C (ENNReal.ofReal c)] at hunit
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hc0 hcT).mp (by simpa only [mul_comm] using hunit)

end HarmonicBalls
