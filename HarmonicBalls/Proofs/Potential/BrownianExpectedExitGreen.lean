import HarmonicBalls.Proofs.Potential.GreenOccupationBoundary

/-! # Brownian mean exit time and the Green kernel

The mean exit time is the integral of twice the Green kernel.
-/

open MeasureTheory Set MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal

namespace HarmonicBalls.GreenOccupation

/-- The expected exit time is the total mass of the occupation measure. -/
theorem lintegral_exitTime_eq_occupationMeasure_univ {D : Set ℂ} (hD : IsOpen D)
    (x : ℂ) :
    (∫⁻ p, ContinuousPath.exitTime D p ∂planarBrownianMotion x) =
      occupationMeasure D hD x Set.univ := by
  rw [planarBrownianMotion_eq_continuousProcess,
    SubMarkovKernelSemigroup.IsConservative.lintegral_exitTime_eq_killedResolvent_zero]
  rw [← lintegral_one, occupationMeasure,
    SubMarkovKernelSemigroup.IsConservative.lintegral_killedPotential _ _ _ _ _ measurable_const]

/-- For every starting point, mean exit time is the integral of the density `2 G`. -/
theorem lintegral_exitTime_eq_green {D : Set ℂ} (hD : IsSmoothBoundedOpen D) (x : ℂ) :
    (∫⁻ p, ContinuousPath.exitTime D p ∂planarBrownianMotion x) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hm : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [lintegral_exitTime_eq_occupationMeasure_univ hDo x,
    occupationMeasure_eq_greenMeasure_all hD x, greenMeasure, ← lintegral_one,
    lintegral_withDensity_eq_lintegral_mul₀' hm measurable_const.aemeasurable]
  simp only [Pi.mul_apply, mul_one]

/-- Mean exit time as the extended-nonnegative image of the real Green integral. -/
theorem lintegral_exitTime_eq_ofReal_green {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) :
    (∫⁻ p, ContinuousPath.exitTime D p ∂planarBrownianMotion x) =
      ENNReal.ofReal (2 * ∫ y in D, greenFunction D x y) := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hi := (integrable_greenFunction_pole hDo hD.1 x).const_mul 2
  have hn : ∀ᵐ y : ℂ, 0 ≤ 2 * greenFunction D x y :=
    Filter.Eventually.of_forall fun y => mul_nonneg (by norm_num) (greenFunction_nonneg hD.1 x y)
  rw [lintegral_exitTime_eq_green hD x, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_const_mul, ← integral_indicator hDo.measurableSet]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ D
  · simp [hy]
  · simp [hy, greenFunction_of_notMem_right hy]

/-- The real expected exit time is twice the Green integral. -/
theorem integral_exitTime_toReal_eq_green {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) :
    (∫ p, (ContinuousPath.exitTime D p).toReal ∂planarBrownianMotion x) =
      2 * ∫ y in D, greenFunction D x y := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hf := lintegral_exitTime_planarBrownianMotion_lt_top hDo hD.1 x
  have hmeas := ContinuousPath.measurable_exitTime D hDo
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hf.ne),
    lintegral_exitTime_eq_ofReal_green hD x, ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (integral_nonneg fun y => greenFunction_nonneg hD.1 x y)

/-- The Green density has finite integral for every starting point. -/
theorem lintegral_green_density_lt_top {D : Set ℂ} (hD : IsSmoothBoundedOpen D) (x : ℂ) :
    (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y)) < ⊤ := by
  rw [← lintegral_exitTime_eq_green hD x]
  exact lintegral_exitTime_planarBrownianMotion_lt_top
    (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) hD.1 x

/-- The real-valued Brownian exit time is integrable. -/
theorem integrable_exitTime_toReal {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) :
    Integrable (fun p => (ContinuousPath.exitTime D p).toReal) (planarBrownianMotion x) := by
  exact integrable_toReal_of_lintegral_ne_top
    (ContinuousPath.measurable_exitTime D hD).aemeasurable
    (lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x).ne

end HarmonicBalls.GreenOccupation
