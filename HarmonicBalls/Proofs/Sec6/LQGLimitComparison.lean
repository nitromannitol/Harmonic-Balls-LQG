import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Local comparison of vague LQG limits -/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Local inequalities on nonnegative continuous tests imply the same
inequality for compact sets. -/
theorem measure_compact_le_of_integral_le_of_tsupport_subset
    {U : Set ℂ} (hU : IsOpen U) {ν ν' : Measure ℂ}
    [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ν']
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x, 0 ≤ f x) → ∫ x, f x ∂ν ≤ ∫ x, f x ∂ν')
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) : ν K ≤ ν' K := by
  rw [hK.measure_eq_iInf_isOpen (μ := ν')]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  obtain ⟨f, hf1, hfc, hfV, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter hU) (subset_inter hKV hKU)
  have hfint : ∀ μ : Measure ℂ, [IsLocallyFiniteMeasure μ] → Integrable (f : ℂ → ℝ) μ :=
    fun μ _ => f.continuous.integrable_of_hasCompactSupport hfc
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have h1 : ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν) (Eventually.of_forall hnn)]
    calc ν K = ∫⁻ x, K.indicator 1 x ∂ν := by rw [lintegral_indicator_one hK.measurableSet]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp [hx, hf1 hx]
        · simp [hx]
  have h2 : ENNReal.ofReal (∫ x, f x ∂ν') ≤ ν' (V ∩ U) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hfint ν') (Eventually.of_forall hnn)]
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν' ≤ ∫⁻ x, (V ∩ U).indicator 1 x ∂ν' := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ V ∩ U
          · have := (hf01 x).2
            simp [hx, this]
          · have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfV hx'))
            simp [hx, this]
      _ = ν' (V ∩ U) := by rw [lintegral_indicator_one (hV.inter hU).measurableSet]
  calc ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) := h1
    _ ≤ ENNReal.ofReal (∫ x, f x ∂ν') :=
      ENNReal.ofReal_le_ofReal (h f f.continuous hfc (hfV.trans inter_subset_right) hnn)
    _ ≤ ν' (V ∩ U) := h2
    _ ≤ ν' V := measure_mono inter_subset_left

/-- If the regularized fields are eventually ordered on each compact subset
of an open set, their vague-limit measures are ordered on compact subsets. -/
theorem isLQGLimit_measure_compact_le {γ : ℝ} (hγ : 0 ≤ γ)
    {hε hε' : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (hm : IsLQGLimit γ hε m) (hm' : IsLQGLimit γ hε' m')
    (hc' : ∀ k, Continuous (hε' (dyadicScale k)))
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hloc : ∀ L : Set ℂ, IsCompact L → L ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ L, hε (dyadicScale k) z ≤ hε' (dyadicScale k) z) :
    m K ≤ m' K := by
  let : IsLocallyFiniteMeasure m := hm.isLocallyFiniteMeasure
  let : IsLocallyFiniteMeasure m' := hm'.isLocallyFiniteMeasure
  apply measure_compact_le_of_integral_le_of_tsupport_subset hU _ hK hKU
  intro f hf hfc hfU hnn
  have hmeas : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hzero : ∀ ν : Measure ℂ, ∫ x, f x ∂ν = ∫ x in tsupport f, f x ∂ν := fun ν =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport hx).symm
  have hle : ∀ᶠ k : ℕ in atTop,
      (∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) ≤
        ∫ z, f z ∂(lqgApprox γ hε' (dyadicScale k)) := by
    filter_upwards [hloc _ hfc hfU] with k hk
    let : IsLocallyFiniteMeasure (lqgApprox γ hε' (dyadicScale k)) :=
      isLocallyFiniteMeasure_lqgApprox_of_continuous γ hε' (dyadicScale k) (hc' k)
    have hmeasure : (lqgApprox γ hε (dyadicScale k)).restrict (tsupport f) ≤
        (lqgApprox γ hε' (dyadicScale k)).restrict (tsupport f) := by
      simp only [lqgApprox]
      rw [restrict_withDensity hmeas, restrict_withDensity hmeas]
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hmeas] with z hz
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hk z hz) hγ))
        (Real.rpow_nonneg (dyadicScale_pos k).le _)
    rw [hzero (lqgApprox γ hε (dyadicScale k)), hzero (lqgApprox γ hε' (dyadicScale k))]
    exact integral_mono_measure hmeasure (Eventually.of_forall hnn)
      ((hf.integrable_of_hasCompactSupport hfc).mono_measure Measure.restrict_le_self)
  exact le_of_tendsto_of_tendsto (hm.tendsto_integral f hf hfc) (hm'.tendsto_integral f hf hfc) hle

end HarmonicBalls.Section6
