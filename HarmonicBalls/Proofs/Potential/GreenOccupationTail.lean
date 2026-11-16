import HarmonicBalls.Proofs.Potential.GreenOccupationFiniteHorizon

/-! # Killed Brownian occupation tails

Expected occupation after a deterministic horizon vanishes for bounded observables.
-/

open MeasureTheory Set Filter MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal Topology

namespace HarmonicBalls.GreenOccupation

/-- The expected occupation after time `T` tends to zero for every bounded
nonnegative measurable observable and every starting point. -/
theorem tendsto_occupation_tail {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ⊤) (hfC : ∀ y, f y ≤ C) :
    Tendsto (fun T : ℝ => ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      (Set.Ioi T).indicator (fun t =>
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x)
      atTop (𝓝 0) := by
  let μ := planarBrownianMotion x
  let ν := volume.restrict (Set.Ioi (0 : ℝ))
  let g : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p =>
    {p : ContinuousPath ℂ × ℝ |
      ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
      (fun p => f (p.1 (Real.toNNReal p.2))) p
  have heval : Measurable fun p : ContinuousPath ℂ × ℝ => p.1 (Real.toNNReal p.2) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hS : MeasurableSet {p : ContinuousPath ℂ × ℝ |
      ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hD).comp measurable_fst)
  have hg : Measurable g := (hf.comp heval).indicator hS
  have hfinite : (∫⁻ p, g p ∂(μ.prod ν)) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_prod _ hg.aemeasurable]
    change (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
        (fun t => f (p (Real.toNNReal t))) t) ∂planarBrownianMotion x) ≠ ⊤
    rw [← lintegral_occupationMeasure hD x hf]
    let := isFiniteMeasure_occupationMeasure hD hDb x
    exact ne_top_of_le_ne_top (lintegral_const_lt_top hC).ne
      (lintegral_mono hfC)
  let F : ℝ → ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun T p =>
    {p : ContinuousPath ℂ × ℝ | T < p.2}.indicator g p
  have hF (T : ℝ) : Measurable (F T) :=
    hg.indicator (measurableSet_lt measurable_const measurable_snd)
  have hlim : ∀ p, Tendsto (fun T : ℝ => F T p) atTop (𝓝 0) := by
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop p.2] with T hT
    simp [F, not_lt_of_ge hT]
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ.prod ν) (l := atTop) (f := fun _ => 0) g
    (Eventually.of_forall hF)
    (Eventually.of_forall fun T => Eventually.of_forall fun p =>
      by by_cases hp : T < p.2 <;> simp [F, hp])
    hfinite (Eventually.of_forall hlim)
  simp only [lintegral_zero] at h
  have heq (T : ℝ) : (∫⁻ p, F T p ∂(μ.prod ν)) =
      ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
        (Set.Ioi T).indicator (fun t =>
          {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
            (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x := by
    rw [MeasureTheory.lintegral_prod _ (hF T).aemeasurable]
    rfl
  simpa only [heq] using h

end HarmonicBalls.GreenOccupation
