import HarmonicBalls.Proofs.Potential.GreenOccupationTailBound

/-! # Signed Brownian occupation and Green integrals

Real bounded observables of killed Brownian occupation.
-/

open MeasureTheory Set MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal

namespace HarmonicBalls.GreenOccupation

/-- A bounded measurable observable is integrable against the occupation measure,
with integral given by the Green density. -/
theorem integrable_occupationMeasure_and_green {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) :
    Integrable f (occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x) ∧
    Integrable (fun y => (2 * greenFunction D x y) * f y) volume ∧
    (∫ y, f y ∂occupationMeasure D (GreenGeneral.isOpen_of_isSmoothBoundedOpen hD) x) =
      ∫ y, (2 * greenFunction D x y) * f y := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let := isFiniteMeasure_occupationMeasure hDo hD.1 x
  have hi : Integrable f (occupationMeasure D hDo x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hfC y)
  have hm : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have ht : ∀ᵐ y ∂volume, ENNReal.ofReal (2 * greenFunction D x y) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have heq : ∀ y, (ENNReal.ofReal (2 * greenFunction D x y)).toReal =
      2 * greenFunction D x y := by
    intro y
    rw [ENNReal.toReal_ofReal]
    exact mul_nonneg (by norm_num) (greenFunction_nonneg hD.1 x y)
  have hig : Integrable f (volume.withDensity (fun y => ENNReal.ofReal (2 * greenFunction D x y))) := by
    change Integrable f (greenMeasure D x)
    rw [← occupationMeasure_eq_greenMeasure_all hD x]
    exact hi
  refine ⟨hi, ?_, ?_⟩
  · have hh := (integrable_withDensity_iff_integrable_smul₀' hm ht).mp hig
    simpa only [heq, smul_eq_mul] using hh
  · rw [occupationMeasure_eq_greenMeasure_all hD x]
    change (∫ y, f y ∂volume.withDensity (fun y => ENNReal.ofReal (2 * greenFunction D x y))) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hm ht]
    simp only [heq, smul_eq_mul]

/-- The killed path-time observable is integrable and has the same integral
as the occupation measure. -/
theorem integrable_killedPath_and_integral {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) :
    let g : ContinuousPath ℂ × ℝ → ℝ := fun p =>
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun t => f (p.1 (Real.toNNReal t))) p.2
    Integrable g ((planarBrownianMotion x).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (∫ p, (∫ t in Set.Ioi (0 : ℝ), g (p, t)) ∂planarBrownianMotion x) =
      ∫ y, f y ∂occupationMeasure D hD x := by
  let g : ContinuousPath ℂ × ℝ → ℝ := fun p =>
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
      (fun t => f (p.1 (Real.toNNReal t))) p.2
  have heval : Measurable fun p : ContinuousPath ℂ × ℝ => p.1 (Real.toNNReal p.2) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hsurv : MeasurableSet {p : ContinuousPath ℂ × ℝ |
      ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp
      (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst)
  have hg : Measurable g := by
    change Measurable ({p : ContinuousPath ℂ × ℝ |
      ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun p => f (p.1 (Real.toNNReal p.2))))
    exact (hf.comp heval).indicator hsurv
  let μ := planarBrownianMotion x
  let ν := volume.restrict (Set.Ioi (0 : ℝ))
  let := isFiniteMeasure_occupationMeasure hD hDb x
  have hbound : (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
        (fun _ => ENNReal.ofReal C) t) ∂μ) < ⊤ := by
    rw [← lintegral_occupationMeasure hD x measurable_const]
    exact lintegral_const_lt_top ENNReal.ofReal_ne_top
  have hgi : Integrable g (μ.prod ν) := by
    refine ⟨hg.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hg.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ hbound
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro t
    by_cases ht : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p
    · simpa [g, ht, Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hfC (p (Real.toNNReal t)))
    · simp [g, ht]
  have hfi : Integrable f (occupationMeasure D hD x) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hfC y)
  refine ⟨hgi, ?_⟩
  rw [← integral_prod g hgi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
  congr 1
  · rw [lintegral_prod _ (hg.ennreal_ofReal.aemeasurable), lintegral_occupationMeasure hD x hf.ennreal_ofReal]
    congr 1
    apply lintegral_congr
    intro p
    apply lintegral_congr
    intro t
    by_cases ht : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p <;>
      simp [g, ht]
  · have hneg : AEMeasurable (fun z => ENNReal.ofReal (-g z)) (μ.prod ν) :=
      hg.neg.ennreal_ofReal.aemeasurable
    have hnegf : Measurable (fun y => ENNReal.ofReal (-f y)) := hf.neg.ennreal_ofReal
    rw [lintegral_prod _ hneg, lintegral_occupationMeasure hD x hnegf]
    congr 1
    apply lintegral_congr
    intro p
    apply lintegral_congr
    intro t
    by_cases ht : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p <;>
      simp [g, ht]

/-- The signed occupation integral equals the factor-two Green integral, and
its error after a nonnegative horizon is bounded by the expected exit excess. -/
theorem signed_occupation_eq_green_and_error_le {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) (x : ℂ) {f : ℂ → ℝ} (hf : Measurable f)
    {C : ℝ} (hfC : ∀ y, |f y| ≤ C) {T : ℝ} (hT : 0 ≤ T) :
    let g : ContinuousPath ℂ × ℝ → ℝ := fun p =>
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun t => f (p.1 (Real.toNNReal t))) p.2
    let a : ContinuousPath ℂ × ℝ → ℝ := fun p => (Set.Iic T).indicator (fun t => g (p.1, t)) p.2
    Integrable g ((planarBrownianMotion x).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    Integrable a ((planarBrownianMotion x).prod (volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    Integrable (fun p => ∫ t in Set.Ioi (0 : ℝ), g (p, t)) (planarBrownianMotion x) ∧
    Integrable (fun p => ∫ t in Set.Ioi (0 : ℝ), a (p, t)) (planarBrownianMotion x) ∧
    (∫ p, (∫ t in Set.Ioi (0 : ℝ), g (p, t)) ∂planarBrownianMotion x) =
      (∫ y, (2 * greenFunction D x y) * f y) ∧
    ENNReal.ofReal |(∫ y, (2 * greenFunction D x y) * f y) -
      (∫ p, (∫ t in Set.Ioi (0 : ℝ), a (p, t)) ∂planarBrownianMotion x)| ≤
        ENNReal.ofReal C * ∫⁻ p, ContinuousPath.exitTime D p - ENNReal.ofReal T
          ∂planarBrownianMotion x := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let g : ContinuousPath ℂ × ℝ → ℝ := fun p =>
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
      (fun t => f (p.1 (Real.toNNReal t))) p.2
  let S : Set (ContinuousPath ℂ × ℝ) := {p | p.2 ≤ T}
  let a : ContinuousPath ℂ × ℝ → ℝ := S.indicator g
  let b : ContinuousPath ℂ × ℝ → ℝ := Sᶜ.indicator g
  let μ := planarBrownianMotion x
  let ν := volume.restrict (Set.Ioi (0 : ℝ))
  have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_const
  have hg := integrable_killedPath_and_integral hDo hD.1 x hf hfC
  change Integrable g (μ.prod ν) ∧ _ at hg
  have ha : Integrable a (μ.prod ν) := hg.1.indicator hS
  have hb : Integrable b (μ.prod ν) := hg.1.indicator hS.compl
  have hsplit : (∫ p, g p ∂μ.prod ν) = (∫ p, a p ∂μ.prod ν) +
      (∫ p, b p ∂μ.prod ν) := by
    rw [integral_indicator hS, integral_indicator hS.compl]
    exact (integral_add_compl hS hg.1).symm
  have heq := (integrable_occupationMeasure_and_green hD x hf hfC).2.2
  have hid : (∫ p, (∫ t in Set.Ioi (0 : ℝ), g (p, t)) ∂μ) =
      ∫ y, (2 * greenFunction D x y) * f y := hg.2.trans heq
  have hdiff : (∫ y, (2 * greenFunction D x y) * f y) -
      (∫ p, (∫ t in Set.Ioi (0 : ℝ), a (p, t)) ∂μ) =
        ∫ p, b p ∂μ.prod ν := by
    rw [← hid, ← integral_prod g hg.1, ← integral_prod a ha, hsplit]
    ring
  change Integrable g (μ.prod ν) ∧ Integrable a (μ.prod ν) ∧ _
  refine ⟨hg.1, ha, hg.1.integral_prod_left, ha.integral_prod_left, hid, ?_⟩
  change ENNReal.ofReal |(∫ y, (2 * greenFunction D x y) * f y) -
    (∫ p, (∫ t in Set.Ioi (0 : ℝ), a (p, t)) ∂μ)| ≤ _
  rw [hdiff, ← Real.enorm_eq_ofReal_abs]
  calc
    _ ≤ ∫⁻ p, ‖b p‖ₑ ∂μ.prod ν := enorm_integral_le_lintegral_enorm b
    _ = ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), ‖b (p, t)‖ₑ) ∂μ := by
      rw [lintegral_prod _ hb.aestronglyMeasurable.enorm]
    _ ≤ ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      (Set.Ioi T).indicator (fun t =>
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun _ => ENNReal.ofReal C) t) t) ∂μ := by
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro t
      by_cases ht : T < t <;>
        by_cases hs : ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p <;>
        simp [b, S, g, ht, hs, Real.enorm_eq_ofReal_abs,
          ENNReal.ofReal_le_ofReal (hfC (p (Real.toNNReal t)))]
    _ ≤ _ := occupation_tail_le_exitTime_excess hDo x (fun _ => le_rfl) hT

end HarmonicBalls.GreenOccupation
