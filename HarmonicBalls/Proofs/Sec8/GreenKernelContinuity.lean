import HarmonicBalls.Proofs.Sec8.VeryGoodGreenMeasurable
import HarmonicBalls.Proofs.SecA.Basic

/-! # The extended Green kernel at the pole

The Green function of a disc diverges logarithmically at the pole. Giving it
value infinity there produces a continuous extended-nonnegative kernel.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- The Green function of a disc tends to infinity at its pole. -/
theorem tendsto_greenFunction_ball_pole {R : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    Tendsto (fun x : ℂ => greenFunction (ball (0 : ℂ) R) z x) (𝓝[≠] z) atTop := by
  have hz' : ‖z‖ < R := by simpa using hz
  have hr : 0 < (R - ‖z‖) / 3 := by linarith
  have hnorm : Tendsto (fun x : ℂ => ‖x - z‖) (𝓝[≠] z) (𝓝[>] 0) :=
    tendsto_norm_sub_self_nhdsNE z
  have hlog : Tendsto (fun x : ℂ => Real.log ‖x - z‖) (𝓝[≠] z) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hnorm
  have hbound : Tendsto (fun x : ℂ => (2 * Real.pi)⁻¹ *
      (Real.log ‖x - z‖ - Real.log ((R - ‖z‖) / 3))) (𝓝[≠] z) atBot := by
    exact (tendsto_atBot_add_const_right _ _ hlog).const_mul_atBot (by positivity)
  have hneg : Tendsto (fun x : ℂ => -greenFunction (ball (0 : ℂ) R) z x)
      (𝓝[≠] z) atBot := by
    apply tendsto_atBot_mono' _ _ hbound
    have hev : ∀ᶠ x in 𝓝[≠] z, 0 < ‖x - z‖ ∧ ‖x - z‖ < (R - ‖z‖) / 3 :=
      hnorm.eventually (Ioo_mem_nhdsGT hr)
    filter_upwards [hev] with x hx
    simpa using neg_mul_greenFunction_ball_le (R := R) (z := z) (x := x)
      (t := 1) zero_lt_one hx.1 hx.2
  simpa only [tendsto_neg_atBot_iff] using hneg

/-- The disc Green kernel, with infinity on its diagonal, is continuous in
its first variable throughout the disc. -/
theorem continuousOn_extendedGreenKernel_ball (R : ℝ) (y : ℂ) :
    ContinuousOn (fun x : ℂ => if y = x then (∞ : ℝ≥0∞)
      else ENNReal.ofReal (greenFunction (ball 0 R) x y)) (ball 0 R) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hy : y ∈ ball (0 : ℂ) R
  · by_cases hxy : x = y
    · subst x
      apply continuousAt_iff_punctured_nhds.mpr
      simp only [ite_true]
      apply (ENNReal.tendsto_ofReal_atTop.comp (tendsto_greenFunction_ball_pole hy)).congr'
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hwy : w ≠ y := by simpa using hw
      simp only [Ne.symm hwy, ite_false, greenFunction_ball_comm R, Function.comp_apply]
    · have hcont : ContinuousAt (fun w : ℂ => ENNReal.ofReal (greenFunction (ball 0 R) y w)) x :=
        ENNReal.continuous_ofReal.continuousAt.comp
          ((continuousOn_greenFunction_ball hy).continuousAt
            (isOpen_compl_singleton.mem_nhds (by simpa using hxy)))
      apply hcont.congr
      filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ {y}ᶜ by simpa using hxy)] with w hw
      have hwy : w ≠ y := by simpa using hw
      simp only [Ne.symm hwy, ite_false, greenFunction_ball_comm R]
  · have hcont : ContinuousAt (fun _ : ℂ => (0 : ℝ≥0∞)) x := continuousAt_const
    apply hcont.congr
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    have hyw : y ≠ w := fun h => hy (h ▸ hw)
    simp only [hyw, ite_false, greenFunction_of_notMem_right hy, ENNReal.ofReal_zero]

/-- The Green-potential supremum in the very-good-annulus condition at the
origin is a measurable function of the measure. -/
theorem measurable_annulusGreenPotentialSup_zero (ρ : ℝ) :
    Measurable (fun μ : Measure ℂ => annulusGreenPotentialSup μ 0 (ρ / 4) (2 * ρ)) := by
  apply measurable_annulusGreenPotentialSup_of_lowerSemicontinuous
  intro μ
  apply lowerSemicontinuous_lintegral_of_sections
  · intro x
    exact Measurable.ite (measurableSet_singleton (x : ℂ)) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  · intro y
    have hc := (continuousOn_extendedGreenKernel_ball (2 * ρ) y).mono
      (show annulus (0 : ℂ) (ρ / 4) (2 * ρ) ⊆ ball 0 (2 * ρ) by
        exact sdiff_subset)
    exact (continuousOn_iff_continuous_domRestrict.mp hc).lowerSemicontinuous

/-- The normalized Green-potential size in the very-good-annulus condition at
the origin is a measurable function of the measure. -/
theorem measurable_annulusGreenPotentialRatio_zero (ρ : ℝ) :
    Measurable (fun μ : Measure ℂ =>
      annulusGreenPotentialSup μ 0 (ρ / 4) (2 * ρ) / μ (annulus 0 (ρ / 4) (2 * ρ))) := by
  exact (measurable_annulusGreenPotentialSup_zero ρ).div
    (Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet)

/-- At the origin, measurability of the ball-mass size ratio and the
individual good-annulus events suffices for the full very-good event. -/
theorem measurableSet_isVeryGoodAnnulus_zero_of_measurable_parts
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hball : Measurable (fun μ : Measure ℂ =>
      annulusBallMassSize μ βminus ρ 0 / μ (annulus 0 (ρ / 4) (2 * ρ))))
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), MeasurableSet {μ : Measure ℂ |
      IsGoodAnnulus μ (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b}) :
    MeasurableSet {μ : Measure ℂ |
      IsVeryGoodAnnulus μ βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} :=
  measurableSet_isVeryGoodAnnulus_of_measurable_parts βminus ρ hρ 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ hball (measurable_annulusGreenPotentialRatio_zero ρ) hgood

end HarmonicBalls
