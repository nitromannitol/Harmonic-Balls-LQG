import HarmonicBalls.Proofs.Potential.BrownianExitTimeExcess
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen

/-! # Quantitative killed Brownian occupation tails

Bounds for the occupation remaining after a deterministic time.
-/

open MeasureTheory Set MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal

namespace HarmonicBalls.GreenOccupation

/-- The expected occupation after a nonnegative horizon is bounded by the
observable bound times the expected excess of the exit time. -/
theorem occupation_tail_le_exitTime_excess {D : Set ℂ} (hD : IsOpen D)
    (x : ℂ) {f : ℂ → ℝ≥0∞} {C : ℝ≥0∞} (hfC : ∀ y, f y ≤ C)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      (Set.Ioi T).indicator (fun t =>
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x) ≤
      C * ∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T ∂planarBrownianMotion x := by
  rw [lintegral_exitTime_sub_eq_occupation_tail x hT]
  let g : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    (Set.Ioi T).indicator (fun t =>
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun _ => (1 : ℝ≥0∞)) t) p.2
  have hg : Measurable g := by
    change Measurable (fun p : ContinuousPath ℂ × ℝ =>
      {p : ContinuousPath ℂ × ℝ | T < p.2}.indicator
        ({p : ContinuousPath ℂ × ℝ |
          ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
          (fun _ => (1 : ℝ≥0∞))) p)
    exact (measurable_const.indicator (measurableSet_lt
      (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst))).indicator
        (measurableSet_lt measurable_const measurable_snd)
  have hi (p : ContinuousPath ℂ) : Measurable (fun t => g (p, t)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  have ho : Measurable (fun p => ∫⁻ t in Set.Ioi (0 : ℝ), g (p, t)) :=
    hg.lintegral_prod_right
  calc
    _ ≤ ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), C * g (p, t)) ∂planarBrownianMotion x := by
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro t
      by_cases ht : T < t <;>
        by_cases hs : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p <;>
        simp [g, ht, hs, hfC]
    _ = C * ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), g (p, t)) ∂planarBrownianMotion x := by
      simp_rw [lintegral_const_mul C (hi _)]
      exact lintegral_const_mul C ho

/-- The Green integral is finite, and its finite-horizon error is bounded by
`C` times the expected exit-time excess. -/
theorem green_finite_horizon_error_le {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hfC : ∀ y, f y ≤ C) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y) < ⊤ ∧
    (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y) -
      (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        (Set.Iic T).indicator (fun t =>
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
            (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x) ≤
      C * ∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T ∂planarBrownianMotion x := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let g : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
      (fun t => f (p.1 (Real.toNNReal t))) p.2
  have heval : Measurable fun p : ContinuousPath ℂ × ℝ => p.1 (Real.toNNReal p.2) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hg : Measurable g := by
    change Measurable (fun p : ContinuousPath ℂ × ℝ =>
      {p : ContinuousPath ℂ × ℝ |
        ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun p => f (p.1 (Real.toNNReal p.2))) p)
    exact (hf.comp heval).indicator (measurableSet_lt
      (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hDo).comp measurable_fst))
  let a : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    {p : ContinuousPath ℂ × ℝ | p.2 ≤ T}.indicator g p
  let b : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    {p : ContinuousPath ℂ × ℝ | T < p.2}.indicator g p
  have ha : Measurable a := hg.indicator (measurableSet_le measurable_snd measurable_const)
  have hao : Measurable (fun p => ∫⁻ t in Set.Ioi (0 : ℝ), a (p, t)) :=
    ha.lintegral_prod_right
  have hsplit (p : ContinuousPath ℂ) :
      (∫⁻ t in Set.Ioi (0 : ℝ), g (p, t)) =
        (∫⁻ t in Set.Ioi (0 : ℝ), a (p, t)) +
        (∫⁻ t in Set.Ioi (0 : ℝ), b (p, t)) := by
    have hpa : Measurable (fun t => a (p, t)) := ha.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_add_left hpa]
    apply lintegral_congr
    intro t
    by_cases ht : t ≤ T <;> simp [a, b, ht, not_lt_of_ge, lt_of_not_ge]
  have hidentity : (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), g (p, t))
      ∂planarBrownianMotion x) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y := by
    dsimp only [g]
    rw [← lintegral_occupationMeasure hDo x hf, occupationMeasure_eq_greenMeasure_all hD x]
    have hm : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
      ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    exact lintegral_withDensity_eq_lintegral_mul₀' hm hf.aemeasurable
  have hfin : (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y) < ⊤ := by
    rw [← hidentity]
    dsimp only [g]
    rw [← lintegral_occupationMeasure hDo x hf]
    let := isFiniteMeasure_occupationMeasure hDo hD.1 x
    exact lt_of_le_of_lt (lintegral_mono hfC) (lintegral_const_lt_top hC)
  have hdecomp : (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y) =
      (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), a (p, t)) ∂planarBrownianMotion x) +
      (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), b (p, t)) ∂planarBrownianMotion x) := by
    rw [← hidentity]
    simp_rw [hsplit]
    exact lintegral_add_left hao _
  refine ⟨hfin, ?_⟩
  change (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y) -
    (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), a (p, t)) ∂planarBrownianMotion x) ≤ _
  rw [hdecomp]
  calc
    _ ≤ ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), b (p, t)) ∂planarBrownianMotion x :=
      tsub_le_iff_right.mpr (by rw [add_comm])
    _ ≤ _ := occupation_tail_le_exitTime_excess hDo x hfC hT

end HarmonicBalls.GreenOccupation
