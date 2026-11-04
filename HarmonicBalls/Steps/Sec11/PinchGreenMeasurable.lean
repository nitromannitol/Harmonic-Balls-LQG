import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Measurability of the annular Green-potential supremum -/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- Translation of a ball preserves its Green function. -/
theorem greenFunction_ball_translate (z x y : ℂ) (R : ℝ) :
    greenFunction (ball z R) x y = greenFunction (ball 0 R) (x - z) (y - z) := by
  have hball : (fun w : ℂ => w + z) '' ball 0 R = ball z R := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hu
    · intro hw
      refine ⟨w - z, ?_, sub_add_cancel w z⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hw
  have h := Section6.greenFunction_translate (ball 0 R) z (x - z) (y - z)
  simpa only [hball, sub_add_cancel] using h

/-- The extended Green kernel of a translated disc is continuous in its pole. -/
theorem continuousOn_extendedGreenKernel_ball_centered (z : ℂ) (R : ℝ) (y : ℂ) :
    ContinuousOn (fun x : ℂ => if y = x then (∞ : ℝ≥0∞)
      else ENNReal.ofReal (greenFunction (ball z R) x y)) (ball z R) := by
  have hc := continuousOn_extendedGreenKernel_ball R (y - z)
  have hcomp := hc.comp (continuous_id.sub continuous_const).continuousOn
    (show MapsTo (fun x : ℂ => x - z) (ball z R) (ball 0 R) by
      intro x hx
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hx)
  apply hcomp.congr
  intro x hx
  simp only [Function.comp_apply]
  rw [greenFunction_ball_translate z x y]
  simp only [Pi.sub_apply, id_eq]
  simp only [sub_left_inj]

/-- The Green-potential supremum over any annulus is measurable in the measure. -/
theorem measurable_annulusGreenPotentialSup (z : ℂ) (a b : ℝ) :
    Measurable (fun μ : Measure ℂ => annulusGreenPotentialSup μ z a b) := by
  apply measurable_annulusGreenPotentialSup_of_lowerSemicontinuous
  intro μ
  apply lowerSemicontinuous_lintegral_of_sections
  · intro x
    exact Measurable.ite (measurableSet_singleton (x : ℂ)) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  · intro y
    have hc := (continuousOn_extendedGreenKernel_ball_centered z b y).mono
      (show annulus z a b ⊆ ball z b by exact sdiff_subset)
    exact (continuousOn_iff_continuous_domRestrict.mp hc).lowerSemicontinuous

end HarmonicBalls
