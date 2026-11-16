import HarmonicBalls.Proofs.Potential.GreenOccupationBoundary

/-! # Finite-horizon Brownian occupation

Finite-horizon killed Brownian occupation converges to the Green potential.
-/

open MeasureTheory Set Filter MarkovProcess HarmonicBalls HarmonicBalls.Section6
open scoped ENNReal Topology

namespace HarmonicBalls.GreenOccupation

/-- Expected occupation before exit and before time n increases to the
Green potential, for every starting point, using the zero-diagonal representative. -/
theorem tendsto_finite_horizon_occupation {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Tendsto (fun n : ℕ => ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      (Set.Iic (n : ℝ)).indicator (fun t =>
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x)
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y)) := by
  let hDo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  let g : ContinuousPath ℂ → ℝ → ℝ≥0∞ := fun p t =>
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
      (fun t => f (p (Real.toNNReal t))) t
  have heval : Measurable fun p : ContinuousPath ℂ × ℝ => p.1 (Real.toNNReal p.2) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hS : MeasurableSet {p : ContinuousPath ℂ × ℝ |
      ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_snd))
      ((ContinuousPath.measurable_exitTime D hDo).comp measurable_fst)
  have hg : Measurable (fun p : ContinuousPath ℂ × ℝ => g p.1 p.2) := by
    change Measurable (fun p : ContinuousPath ℂ × ℝ =>
      {p : ContinuousPath ℂ × ℝ |
        ((Real.toNNReal p.2 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p.1}.indicator
        (fun p => f (p.1 (Real.toNNReal p.2))) p)
    exact (hf.comp heval).indicator hS
  have hfinite (n : ℕ) : Measurable (fun p : ContinuousPath ℂ =>
      ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Iic (n : ℝ)).indicator (g p) t) := by
    apply Measurable.lintegral_prod_right
    change Measurable (fun p : ContinuousPath ℂ × ℝ =>
      {p : ContinuousPath ℂ × ℝ | p.2 ≤ (n : ℝ)}.indicator (fun p => g p.1 p.2) p)
    exact hg.indicator (measurableSet_le measurable_snd measurable_const)
  have hmono (p : ContinuousPath ℂ) (t : ℝ) :
      Monotone fun n : ℕ => (Set.Iic (n : ℝ)).indicator (g p) t := by
    intro i j hij
    exact Set.indicator_le_indicator_of_subset (Set.Iic_subset_Iic.mpr (by exact_mod_cast hij)) (by intro _; exact bot_le) t
  have hlim (p : ContinuousPath ℂ) :
      Tendsto (fun n : ℕ => ∫⁻ t in Set.Ioi (0 : ℝ),
        (Set.Iic (n : ℝ)).indicator (g p) t) atTop
        (𝓝 (∫⁻ t in Set.Ioi (0 : ℝ), g p t)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (((hg.comp (measurable_const.prodMk measurable_id)).indicator measurableSet_Iic).aemeasurable)
    · exact Filter.Eventually.of_forall (hmono p)
    · apply Filter.Eventually.of_forall
      intro t
      obtain ⟨N, hN⟩ := exists_nat_ge t
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [Set.indicator_of_mem (by exact le_trans hN (by exact_mod_cast hn))]
  have houter := lintegral_tendsto_of_tendsto_of_monotone
    (μ := planarBrownianMotion x) (fun n => (hfinite n).aemeasurable)
    (Filter.Eventually.of_forall (fun p i j hij => lintegral_mono (fun t => hmono p t hij)))
    (Filter.Eventually.of_forall hlim)
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (2 * greenFunction D x y)) volume :=
    ((integrable_greenFunction_pole hDo hD.1 x).const_mul 2).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hidentity : (∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ), g p t) ∂planarBrownianMotion x) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y := by
    rw [← lintegral_occupationMeasure hDo x hf, occupationMeasure_eq_greenMeasure_all hD x]
    exact lintegral_withDensity_eq_lintegral_mul₀' hmeas hf.aemeasurable
  simpa only [g, hidentity] using houter


/-- The expected killed occupation is increasing in the real time horizon and
converges to twice the Green potential as that horizon tends to infinity. -/
theorem monotone_tendsto_occupation {D : Set ℂ} (hD : IsSmoothBoundedOpen D)
    (x : ℂ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    let F : ℝ → ℝ≥0∞ := fun T => ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
      (Set.Iic T).indicator (fun t =>
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
          (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x
    Monotone F ∧ Tendsto F atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y)) := by
  dsimp only
  let F : ℝ → ℝ≥0∞ := fun T => ∫⁻ p, (∫⁻ t in Set.Ioi (0 : ℝ),
    (Set.Iic T).indicator (fun t =>
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime D p}.indicator
        (fun t => f (p (Real.toNNReal t))) t) t) ∂planarBrownianMotion x
  change Monotone F ∧ Tendsto F atTop _
  have hmono : Monotone F := by
    intro a b hab
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro t
    exact Set.indicator_le_indicator_of_subset (Set.Iic_subset_Iic.mpr hab)
      (by intro _; exact bot_le) t
  refine ⟨hmono, ?_⟩
  have heq : (⨆ T, F T) = ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y := by
    have hnat : Tendsto (fun n : ℕ => F n) atTop
        (𝓝 (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) * f y)) :=
      tendsto_finite_horizon_occupation hD x hf
    have hi := tendsto_atTop_iSup (hmono.comp (Nat.mono_cast : Monotone (fun n : ℕ => (n : ℝ))))
    have hs : (⨆ n : ℕ, F n) = ⨆ T, F T :=
      hmono.iSup_comp_tendsto_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    change Tendsto (fun n : ℕ => F n) atTop (𝓝 (⨆ n : ℕ, F n)) at hi
    rw [hs] at hi
    exact tendsto_nhds_unique hi hnat
  simpa only [heq] using tendsto_atTop_iSup hmono

end HarmonicBalls.GreenOccupation
