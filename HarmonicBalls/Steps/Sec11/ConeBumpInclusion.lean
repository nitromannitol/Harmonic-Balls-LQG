import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift

/-! # The bump inclusion for the cone mass event -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A bump which is constant on the inner annulus and vanishes on the outer
annulus multiplies the cone mass and leaves the Green supremum unchanged. -/
theorem coneMassEvent_of_bump
    (μ : Measure ℂ) (Q : Set ℂ) (M r γ c : ℝ) (z : ℂ) (f : ℂ → ℝ)
    (hQ : MeasurableSet Q)
    (hinner : ∀ x ∈ annulus z r (2 * r), f x = c)
    (houter : ∀ x ∈ annulus z (3 * r) (6 * r), f x = 0)
    {C₁ C₂ : ℝ≥0∞}
    (hmass : C₁ ≤ μ (annulus z r (2 * r) ∩ coneAt Q z))
    (hgreen : annulusGreenPotentialSup μ z (3 * r) (6 * r) ≤ C₂)
    (hheight : ENNReal.ofReal M * C₂ ≤ ENNReal.ofReal (Real.exp (γ * c)) * C₁) :
    coneMassEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) Q M r z := by
  let S := annulus z r (2 * r) ∩ coneAt Q z
  have hS : MeasurableSet S := by
    apply MeasurableSet.inter (measurableSet_ball.diff measurableSet_closedBall)
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image.mpr hQ
  have hrestrict := restrict_withDensity_exp_eq_of_eq_zero μ γ f
    (measurableSet_ball.diff measurableSet_closedBall) houter
  have hg := (annulusGreenPotentialSup_eq_of_restrict_eq z (3 * r) (6 * r) hrestrict)
  have hm : (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) S =
      ENNReal.ofReal (Real.exp (γ * c)) * μ S := by
    rw [withDensity_apply _ hS]
    rw [lintegral_congr_ae (show (fun x => ENNReal.ofReal (Real.exp (γ * f x))) =ᵐ[μ.restrict S]
      (fun _ => ENNReal.ofReal (Real.exp (γ * c))) from by
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [hinner x hx.1])]
    simp
  change ENNReal.ofReal M * annulusGreenPotentialSup _ z (3 * r) (6 * r) ≤ _
  rw [hg, hm]
  calc
    _ ≤ ENNReal.ofReal M * C₂ := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp (γ * c)) * C₁ := hheight
    _ ≤ ENNReal.ofReal (Real.exp (γ * c)) * μ S := by gcongr

end HarmonicBalls

#print axioms HarmonicBalls.coneMassEvent_of_bump
