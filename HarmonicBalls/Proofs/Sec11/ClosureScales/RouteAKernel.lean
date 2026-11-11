import Mathlib

/-! # Route (A) analytic core: integrability of the logarithmic kernel on discs

The covariance kernel of the whole-plane GFF is `wholePlaneCov z w = log(max(|z|,1) max(|w|,1) / |z - w|)`
(`HarmonicBalls/Defs/GFF.lean`). Its logarithmic part is locally integrable in the plane; this file proves
`IntegrableOn (fun w => |log ‖w‖|) (ball 0 R)` by polar coordinates. It is the first input of the L² bound on
pairings of the GFF.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- The radial integral `∫_0^R r |log r| dr` is finite: `r ↦ |r log r|` is continuous on `[0, R]`. -/
theorem lintegral_radial_mul_abs_log_lt_top (R : ℝ) :
    ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r * |Real.log r|) < ⊤ := by
  have hcont : Continuous fun r : ℝ => |r * Real.log r| := Real.continuous_mul_log.abs
  have hint : IntegrableOn (fun r : ℝ => |r * Real.log r|) (Ioo (0 : ℝ) R) :=
    (hcont.integrableOn_Icc (a := 0) (b := R)).mono_set Ioo_subset_Icc_self
  have heq : ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal (r * |Real.log r|)
      = ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal |r * Real.log r| := by
    refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    rw [abs_mul, abs_of_pos hr.1]
  rw [heq]
  exact hint.lintegral_lt_top

/-- `|log ‖w‖|` is locally integrable in the plane: it is integrable on every disc `ball 0 R`
(Lebesgue measure), by polar coordinates `Complex.lintegral_comp_polarCoord_symm`. -/
theorem integrableOn_abs_log_norm_ball (R : ℝ) :
    IntegrableOn (fun w : ℂ => |Real.log ‖w‖|) (ball (0 : ℂ) R) := by
  have hmeas : Measurable fun w : ℂ => |Real.log ‖w‖| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp measurable_norm)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  set G : ℂ → ℝ≥0∞ := (ball (0 : ℂ) R).indicator fun w => ENNReal.ofReal |Real.log ‖w‖| with hG
  have hGint : ∫⁻ w in ball (0 : ℂ) R, ‖|Real.log ‖w‖|‖ₑ = ∫⁻ w, G w := by
    rw [hG, lintegral_indicator measurableSet_ball]
    refine setLIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
    simp only [Real.enorm_eq_ofReal_abs, abs_abs]
  have hkey := Complex.lintegral_comp_polarCoord_symm G
  have hbound : ∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 • G (Complex.polarCoord.symm p)
        ≤ ∫⁻ p : ℝ × ℝ, (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal (q.1 * |Real.log q.1|) * 1) p := by
    refine le_trans (setLIntegral_mono' (Complex.polarCoord.open_target.measurableSet) (fun p hp => ?_))
      (setLIntegral_le_lintegral _ _)
    rw [Complex.polarCoord_target] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hR : p.1 < R
    · have hG' : G (Complex.polarCoord.symm p) = ENNReal.ofReal |Real.log p.1| := by
        rw [hG, indicator_of_mem (by rw [mem_ball, dist_zero_right, hnorm]; exact hR)]
        simp only [hnorm]
      have hind : (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal (q.1 * |Real.log q.1|) * 1) p
          = ENNReal.ofReal (p.1 * |Real.log p.1|) := by
        have hmem : p ∈ Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := mem_prod.mpr ⟨⟨hp1, hR⟩, hp2⟩
        rw [indicator_of_mem hmem, mul_one]
      rw [hG', hind, smul_eq_mul, ← ENNReal.ofReal_mul (le_of_lt hp1), mul_comm]
    · have hG' : G (Complex.polarCoord.symm p) = 0 := by
        rw [hG, indicator_of_notMem (by rw [mem_ball, dist_zero_right, hnorm]; exact hR)]
      rw [hG', smul_zero]
      exact zero_le
  show ∫⁻ a in ball (0 : ℂ) R, ‖|Real.log ‖a‖|‖ₑ < ⊤
  rw [hGint, ← hkey]
  refine lt_of_le_of_lt hbound ?_
  rw [lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo), Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  have hf : AEMeasurable (fun x : ℝ => ENNReal.ofReal (x * |Real.log x|))
      (volume.restrict (Ioo (0 : ℝ) R)) :=
    ((measurable_id.mul (continuous_abs.measurable.comp Real.measurable_log)).ennreal_ofReal).aemeasurable
  have hg : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    aemeasurable_const
  rw [lintegral_prod_mul hf hg]
  refine ENNReal.mul_lt_top (lintegral_radial_mul_abs_log_lt_top R) ?_
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]
  exact ENNReal.ofReal_lt_top

end HarmonicBalls
