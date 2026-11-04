import HarmonicBalls.Proofs.Sec8.ExhaustionMassConvergence
import HarmonicBalls.Proofs.Sec2.LQGLimitLocality

/-! # Vague convergence and masses of continuity sets -/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Vague convergence of locally finite measures gives the lower
portmanteau bound for every open set. -/
theorem measure_open_le_liminf_of_tendsto_compactlySupported
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {G : Set ℂ} (hG : IsOpen G) : μ G ≤ liminf (fun n => ν n G) atTop := by
  rw [hG.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
  obtain ⟨f, hf1, hfc, hfG, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hG hKG
  have hfcont : Continuous (f : ℂ → ℝ) := f.continuous
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have hint (η : Measure ℂ) [IsLocallyFiniteMeasure η] : Integrable (f : ℂ → ℝ) η :=
    hfcont.integrable_of_hasCompactSupport hfc
  have hlow : μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint μ) (Eventually.of_forall hnn)]
    calc
      μ K = ∫⁻ x, K.indicator 1 x ∂μ := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · simp [hx, hf1 hx]
        · simp [hx]
  have hup (n : ℕ) : ENNReal.ofReal (∫ x, f x ∂(ν n)) ≤ ν n G := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint (ν n)) (Eventually.of_forall hnn)]
    calc
      _ ≤ ∫⁻ x, G.indicator 1 x ∂(ν n) := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ G
        · simp [hx, (hf01 x).2]
        · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfG hx'))
          simp [hx, hzero]
      _ = ν n G := lintegral_indicator_one hG.measurableSet
  have ht := ENNReal.tendsto_ofReal (h f hfcont hfc)
  calc
    μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) := hlow
    _ = liminf (fun n => ENNReal.ofReal (∫ x, f x ∂(ν n))) atTop := ht.liminf_eq.symm
    _ ≤ liminf (fun n => ν n G) atTop := liminf_le_liminf (Eventually.of_forall hup)

/-- Vague convergence of locally finite measures gives the upper
portmanteau bound on compact sets. -/
theorem limsup_measure_compact_le_of_tendsto_compactlySupported
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) : limsup (fun n => ν n K) atTop ≤ μ K := by
  rw [hK.measure_eq_iInf_isOpen (μ := μ)]
  refine le_iInf fun V => le_iInf fun hKV => le_iInf fun hV => ?_
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨f, hf1, hfc, hfV, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter isOpen_ball)
      (subset_inter hKV hKR)
  have hfcont : Continuous (f : ℂ → ℝ) := f.continuous
  have hnn : ∀ x, 0 ≤ f x := fun x => (hf01 x).1
  have hint (η : Measure ℂ) [IsLocallyFiniteMeasure η] : Integrable (f : ℂ → ℝ) η :=
    hfcont.integrable_of_hasCompactSupport hfc
  have hlow (n : ℕ) : ν n K ≤ ENNReal.ofReal (∫ x, f x ∂(ν n)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint (ν n)) (Eventually.of_forall hnn)]
    calc
      ν n K = ∫⁻ x, K.indicator 1 x ∂(ν n) := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂(ν n) := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ K
        · simp [hx, hf1 hx]
        · simp [hx]
  have hup : ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ V := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint μ) (Eventually.of_forall hnn)]
    calc
      _ ≤ ∫⁻ x, V.indicator 1 x ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ V
        · simp [hx, (hf01 x).2]
        · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hx' => hx (hfV hx').1)
          simp [hx, hzero]
      _ = μ V := lintegral_indicator_one hV.measurableSet
  have ht := ENNReal.tendsto_ofReal (h f hfcont hfc)
  calc
    limsup (fun n => ν n K) atTop ≤
        limsup (fun n => ENNReal.ofReal (∫ x, f x ∂(ν n))) atTop :=
      limsup_le_limsup (Eventually.of_forall hlow)
    _ = ENNReal.ofReal (∫ x, f x ∂μ) := ht.limsup_eq
    _ ≤ μ V := hup

/-- A bounded set whose frontier has zero limiting mass is a continuity set
for vague convergence. -/
theorem tendsto_measure_of_tendsto_compactlySupported
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {E : Set ℂ} (hE : Bornology.IsBounded E) (hfrontier : μ (frontier E) = 0) :
    Tendsto (fun n => ν n E) atTop (𝓝 (μ E)) := by
  apply tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
  · simpa only [frontier] using hfrontier
  · exact measure_open_le_liminf_of_tendsto_compactlySupported ν μ h isOpen_interior
  · exact limsup_measure_compact_le_of_tendsto_compactlySupported ν μ h
      (hE.isCompact_closure)

/-- An LQG approximation with a continuous circle-average profile is
locally finite. -/
theorem isLocallyFiniteMeasure_lqgApprox_of_continuous
    (γ : ℝ) (hε : ℝ → ℂ → ℝ) (r : ℝ)
    (hc : Continuous (hε r)) : IsLocallyFiniteMeasure (lqgApprox γ hε r) := by
  let f : ℂ → ℝ := fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z)
  have hf : Continuous f := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  constructor
  intro z
  refine ⟨closedBall z 1, Metric.closedBall_mem_nhds z (by norm_num), ?_⟩
  have hi : IntegrableOn f (closedBall z 1) volume :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall z 1)
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))) (closedBall z 1) < ∞
  rw [withDensity_apply _ isClosed_closedBall.measurableSet]
  exact hi.lintegral_lt_top

/-- For an LQG limit, normalized masses on an increasing bounded exhaustion
converge when the fixed sets involved are continuity sets of the limit. -/
theorem IsLQGLimit.tendsto_normalizedRestriction_exhaustion
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ)
    (hc : ∀ n, Continuous (hε (dyadicScale n))) (E : ℕ → Set ℂ)
    (hmono : Monotone E) (hbounded : Bornology.IsBounded (⋃ n, E n))
    (A : Set ℂ) (hA : MeasurableSet A)
    (hfront : ∀ n, μ (frontier (E n)) = 0 ∧ μ (frontier (A ∩ E n)) = 0)
    (hfrontU : μ (frontier (⋃ n, E n)) = 0 ∧
      μ (frontier (A ∩ ⋃ n, E n)) = 0)
    (hzero : μ (⋃ n, E n) ≠ 0) (htop : μ (⋃ n, E n) ≠ ∞) :
    Tendsto (fun n => normalizedRestriction (lqgApprox γ hε (dyadicScale n)) (E n) A)
      atTop (𝓝 (μ (A ∩ ⋃ n, E n) / μ (⋃ n, E n))) := by
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ hε (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ hε (dyadicScale n) (hc n)
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  have hvague : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)) :=
    hμ.tendsto_integral
  have hfixed (n : ℕ) : Bornology.IsBounded (E n) :=
    hbounded.subset (subset_iUnion E n)
  have hm : ∀ n, Tendsto (fun k => ν k (E n)) atTop (𝓝 (μ (E n))) := fun n =>
    tendsto_measure_of_tendsto_compactlySupported ν μ hvague (hfixed n) (hfront n).1
  have hmA : ∀ n, Tendsto (fun k => ν k (A ∩ E n)) atTop (𝓝 (μ (A ∩ E n))) := fun n =>
    tendsto_measure_of_tendsto_compactlySupported ν μ hvague
      ((hfixed n).subset inter_subset_right) (hfront n).2
  have hmU := tendsto_measure_of_tendsto_compactlySupported ν μ hvague hbounded hfrontU.1
  have hmAU := tendsto_measure_of_tendsto_compactlySupported ν μ hvague
    (hbounded.subset inter_subset_right) hfrontU.2
  have ht := HarmonicBalls.tendsto_normalizedRestriction_exhaustion ν μ E hmono A hzero htop
    hm hmA hmU hmAU
  simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    ENNReal.div_eq_inv_mul] using ht

/-- Centered circle-average versions yield a local mass-ratio version when
the chosen exhaustion consists almost surely of continuity sets of the LQG
measure. -/
theorem exists_local_lqg_ratio_version_of_centered_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : @IsWholePlaneGFF Ω mΩ P hC hcirc)
    (hμ : @IsLQGMeasureOfField Ω mΩ P γ α₀ hcirc μ)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n)) (A : Set ℂ) (hA : MeasurableSet A)
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0 ∧
        μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞)
    (z₀ : ℂ) (d : ℕ → Ω → ℂ → ℝ)
    (hdm : ∀ n, @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _
      (Function.uncurry (d n)))
    (hdeq : ∀ n, ∀ᵐ ω ∂P, ∀ z ∈ E n,
      d n ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z₀) :
    ∃ Y : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ Y ∧
      (fun ω => μ ω (A ∩ ⋃ n, E n) / μ ω (⋃ n, E n)) =ᵐ[P] Y := by
  apply @exists_local_ratio_version_of_centered_approximations Ω mΩ P m γ
    (fun ω => fieldCircleAverage α₀ (hcirc ω)) μ (⋃ n, E n) A hA E hEm z₀
      dyadicScale dyadicScale_pos d hdm hdeq
  let : MeasurableSpace Ω := mΩ
  have hc := ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  filter_upwards [hμ, hc, hfront, hpositive] with ω hω hcω hfrontω hpω
  exact hω.tendsto_normalizedRestriction_exhaustion hcω E hmono hbounded A hA
    hfrontω.1 hfrontω.2 hpω.1 hpω.2

end HarmonicBalls
