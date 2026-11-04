import HarmonicBalls.Proofs.Sec8.VeryGoodCountMeasurable
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-! # Measurability of the Green-potential size

For a fixed pole the nonnegative Green potential is measurable as a function
of the measure. Lower semicontinuity in the pole then makes the supremum over
an annulus measurable, by separability of the annulus.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- Integrating the extended Green kernel over a fixed Borel set is measurable
as a function of the measure. The value at the pole is `∞`. -/
theorem measurable_setLIntegral_greenKernel (x₀ : ℂ) (b : ℝ) (x : ℂ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun μ : Measure ℂ => ∫⁻ y in A,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ) := by
  have hg : Measurable (fun y : ℂ =>
      if y = x then (∞ : ℝ≥0∞) else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) := by
    exact Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  have hrestrict : Measurable (fun μ : Measure ℂ => μ.restrict A) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_coe (hs.inter hA)
  exact (Measure.measurable_lintegral hg).comp hrestrict

/-- Fatou's lemma carries lower semicontinuity through a nonnegative
integral when the parameter space is first countable. -/
theorem lowerSemicontinuous_lintegral_of_sections
    {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [MeasurableSpace Y] (μ : Measure Y) (K : X → Y → ℝ≥0∞)
    (hKmeas : ∀ x, Measurable (K x))
    (hKlsc : ∀ y, LowerSemicontinuous (fun x => K x y)) :
    LowerSemicontinuous (fun x => ∫⁻ y, K x y ∂μ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro x
  calc
    (∫⁻ y, K x y ∂μ) ≤ ∫⁻ y, Filter.liminf (fun x' => K x' y) (nhds x) ∂μ :=
      lintegral_mono (fun y => (hKlsc y).le_liminf x)
    _ ≤ Filter.liminf (fun x' => ∫⁻ y, K x' y ∂μ) (nhds x) :=
      lintegral_liminf_le hKmeas

/-- Lower semicontinuity of the Green potential in the pole makes the
annulus Green-potential supremum measurable in the measure. -/
theorem measurable_annulusGreenPotentialSup_of_lowerSemicontinuous
    (x₀ : ℂ) (a b : ℝ)
    (hsc : ∀ μ : Measure ℂ, LowerSemicontinuous (fun x : annulus x₀ a b =>
      ∫⁻ y in annulus x₀ a b,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ)) :
    Measurable (fun μ : Measure ℂ => annulusGreenPotentialSup μ x₀ a b) := by
  have hA : MeasurableSet (annulus x₀ a b) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hm : Measurable (⨆ x : annulus x₀ a b, fun μ : Measure ℂ =>
      ∫⁻ y in annulus x₀ a b,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro x
      exact measurable_setLIntegral_greenKernel x₀ b x (annulus x₀ a b) hA
    · exact hsc
  convert hm using 1
  funext μ
  simp only [annulusGreenPotentialSup, iSup_apply, iSup_subtype]

/-- Lower semicontinuity also gives measurability of the normalized
Green-potential size used in the very-good-annulus condition. -/
theorem measurable_annulusGreenPotentialRatio_of_lowerSemicontinuous
    (x₀ : ℂ) (ρ : ℝ)
    (hsc : ∀ μ : Measure ℂ, LowerSemicontinuous (fun x : annulus x₀ (ρ / 4) (2 * ρ) =>
      ∫⁻ y in annulus x₀ (ρ / 4) (2 * ρ),
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ (2 * ρ)) x y)) ∂μ)) :
    Measurable (fun μ : Measure ℂ =>
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ))) := by
  exact (measurable_annulusGreenPotentialSup_of_lowerSemicontinuous x₀ (ρ / 4) (2 * ρ) hsc).div
    (Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet)

/-- It suffices to prove lower semicontinuity of the extended Green kernel
in its pole to obtain measurability of the normalized Green size. -/
theorem measurable_annulusGreenPotentialRatio_of_kernel_lowerSemicontinuous
    (x₀ : ℂ) (ρ : ℝ)
    (hkernel : ∀ y : ℂ, LowerSemicontinuous
      (fun x : annulus x₀ (ρ / 4) (2 * ρ) =>
        if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ (2 * ρ)) x y))) :
    Measurable (fun μ : Measure ℂ =>
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ))) := by
  apply measurable_annulusGreenPotentialRatio_of_lowerSemicontinuous
  intro μ
  apply lowerSemicontinuous_lintegral_of_sections
  · intro x
    exact Measurable.ite (measurableSet_singleton (x : ℂ)) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  · exact hkernel

end HarmonicBalls
