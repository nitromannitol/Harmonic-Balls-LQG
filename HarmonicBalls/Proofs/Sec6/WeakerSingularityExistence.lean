import HarmonicBalls.Proofs.Sec6.Section6FromCofinalExistence

/-! # Existence at weaker logarithmic singularities

A limiting measure for a stronger singularity determines the limit for a
weaker one by a continuous nonnegative density. The Section 6 assembly uses
Leonardo Bonanno's proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The explicit literature hypotheses remain subject to operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A weaker logarithmic singularity weights each regularized measure by a
positive power of the truncated distance from the origin. -/
theorem lqgApprox_weaker_singularity {γ α β r : ℝ} (hr : 0 < r)
    (hp : 0 ≤ γ * (β - α)) (hcirc : ℝ → ℂ → ℝ)
    (hc : Continuous (fieldCircleAverage β hcirc r)) :
    lqgApprox γ (fieldCircleAverage α hcirc) r =
      (lqgApprox γ (fieldCircleAverage β hcirc) r).withDensity
        (fun z => ENNReal.ofReal (max r ‖z‖ ^ (γ * (β - α)))) := by
  have ha : Measurable (fun z => ENNReal.ofReal
      (r ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage β hcirc r z))) :=
    ENNReal.measurable_ofReal.comp (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul hc))).measurable
  have hw : Continuous (fun z : ℂ => max r ‖z‖ ^ (γ * (β - α))) :=
    (Real.continuous_rpow_const hp).comp (continuous_const.max continuous_norm)
  have hb : Measurable (fun z => ENNReal.ofReal (max r ‖z‖ ^ (γ * (β - α)))) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  simp only [lqgApprox]
  rw [← withDensity_mul volume ha hb]
  apply withDensity_congr_ae
  filter_upwards [] with z
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _))]
  congr 1
  rw [Real.rpow_def_of_pos (lt_max_of_lt_left hr)]
  have he : γ * fieldCircleAverage α hcirc r z =
      γ * fieldCircleAverage β hcirc r z + Real.log (max r ‖z‖) * (γ * (β - α)) := by
    rw [fieldCircleAverage_eq α hcirc hr, fieldCircleAverage_eq β hcirc hr]
    ring
  rw [he, Real.exp_add]
  ring

/-- Integration against a continuous nonnegative density. -/
theorem integral_withDensity_nonnegative (μ : Measure ℂ) (w φ : ℂ → ℝ)
    (hw : Continuous w) (hw0 : ∀ z, 0 ≤ w z) :
    (∫ z, φ z ∂(μ.withDensity fun z => ENNReal.ofReal (w z))) =
      ∫ z, φ z * w z ∂μ := by
  have hm : Measurable (fun z => ENNReal.ofReal (w z)) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hm (by filter_upwards [] with z; simp) φ]
  congr 1
  funext z
  simp [hw0 z, mul_comm]

/-- Truncated power weights converge uniformly on compact sets after
multiplication by a continuous test function. -/
theorem tendstoUniformlyOn_test_truncated_rpow (p : ℝ) (hp : 0 ≤ p)
    (φ : ℂ → ℝ) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => φ z * max (dyadicScale n) ‖z‖ ^ p)
      (fun z => φ z * ‖z‖ ^ p) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun q : ℝ × ℂ => φ q.2 * max q.1 ‖q.2‖ ^ p) :=
    (hφ.comp continuous_snd).mul ((Real.continuous_rpow_const hp).comp
      (continuous_fst.max (continuous_norm.comp continuous_snd)))
  have hu : UniformContinuousOn
      (fun q : ℝ × ℂ => φ q.2 * max q.1 ‖q.2‖ ^ p) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * max r ‖z‖ ^ p) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * max r ‖z‖ ^ p)
      (fun z => φ z * ‖z‖ ^ p) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, max_eq_right (norm_nonneg _)] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  have hscale : Tendsto dyadicScale atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
  exact hscale.eventually (ht' ε hε)

/-- A limiting LQG measure at a stronger logarithmic singularity constructs
the limiting measure at every weaker singularity. -/
theorem isLQGLimit_of_weaker_singularity {γ α β : ℝ} (hγ : 0 ≤ γ) (hαβ : α ≤ β)
    (hcirc : ℝ → ℂ → ℝ) {ν : Measure ℂ}
    (hν : IsLQGLimit γ (fieldCircleAverage β hcirc) ν)
    (hc : ∀ n, Continuous (fieldCircleAverage β hcirc (dyadicScale n))) :
    IsLQGLimit γ (fieldCircleAverage α hcirc)
      (ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
  let p := γ * (β - α)
  have hp : 0 ≤ p := mul_nonneg hγ (sub_nonneg.mpr hαβ)
  let : IsLocallyFiniteMeasure ν := hν.isLocallyFiniteMeasure
  let νn : ℕ → Measure ℂ := fun n => lqgApprox γ (fieldCircleAverage β hcirc) (dyadicScale n)
  let : ∀ n, IsLocallyFiniteMeasure (νn n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ _ _ (hc n)
  have hw : Continuous (fun z : ℂ => ‖z‖ ^ p) :=
    (Real.continuous_rpow_const hp).comp continuous_norm
  constructor
  · exact IsLocallyFiniteMeasure.withDensity_ofReal hw
  · intro φ hφ hφc
    let K := tsupport φ
    have hK : IsCompact K := hφc
    let g : ℕ → ℂ → ℝ := fun n z => φ z * max (dyadicScale n) ‖z‖ ^ p
    let g₀ : ℂ → ℝ := fun z => φ z * ‖z‖ ^ p
    have hg : ∀ n, Integrable (g n) (νn n) := by
      intro n
      have hgc : Continuous (g n) := hφ.mul ((Real.continuous_rpow_const hp).comp
        (continuous_const.max continuous_norm))
      exact hgc.integrable_of_hasCompactSupport hφc.mul_right
    have huni : TendstoUniformlyOn g g₀ atTop K :=
      tendstoUniformlyOn_test_truncated_rpow p hp φ hφ hK
    have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
      intro n z hz
      have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [g, g₀, hz']
    have hlim := tendsto_integral_of_uniformOn_compact νn ν hν.tendsto_integral hK
      (hφ.mul hw) hφc.mul_right hg huni hoff
    have heq (n : ℕ) : (∫ z, φ z ∂(lqgApprox γ (fieldCircleAverage α hcirc) (dyadicScale n))) =
        ∫ z, g n z ∂(νn n) := by
      rw [lqgApprox_weaker_singularity (dyadicScale_pos n) hp hcirc (hc n)]
      exact integral_withDensity_nonnegative (νn n) _ φ
        ((Real.continuous_rpow_const hp).comp (continuous_const.max continuous_norm))
        (fun z => Real.rpow_nonneg (le_max_of_le_right (norm_nonneg z)) p)
    simp_rw [heq]
    change Tendsto (fun n => ∫ z, g n z ∂(νn n)) atTop
      (𝓝 (∫ z, φ z ∂(ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ p))))
    rw [integral_withDensity_nonnegative ν _ φ hw
      (fun z => Real.rpow_nonneg (norm_nonneg z) p)]
    exact hlim

universe u

/-- Existence at one subcritical strength implies existence at every weaker
strength for the same whole-plane field. -/
theorem lqgMeasureExistence_of_stronger
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α β : ℝ)
    (hαβ : α ≤ β) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    LQGMeasureExistence P γ α hC hcirc := by
  intro hG hγ hγ2 _
  obtain ⟨ν, hν⟩ := hE hG hγ hγ2 hβ
  refine ⟨fun ω => (ν ω).withDensity
    (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))), ?_⟩
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous
      (fieldCircleAverage β (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage β (dyadicScale_pos n))
  filter_upwards [hν, hc] with ω hνω hcω
  exact isLQGLimit_of_weaker_singularity hγ.le hαβ (hcirc ω) hνω hcω

/-- A countable cofinal family of existence assumptions implies existence at
every subcritical singularity. -/
theorem lqgMeasureExistence_of_cofinal
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    LQGMeasureExistence P γ α hC hcirc := by
  intro hG hγ hγ2 hα
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hα)
  let β := lqgQ γ - 1 / ((n : ℝ) + 1)
  have hαβ : α ≤ β := by dsimp [β]; linarith
  have hβ : β < lqgQ γ := by
    dsimp [β]
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  exact lqgMeasureExistence_of_stronger P γ α β hαβ hβ hC hcirc (hE n)
    hG hγ hγ2 hα

/-- The countable cofinal family constructs a limit at every subcritical
strength on one common full-measure event. -/
theorem ae_exists_lqgLimit_for_all_subcritical
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∃ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ := by
  have hex (n : ℕ) : ∃ ν : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hcirc ν := by
    apply hE n hG hγ hγ2
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  let ν : ℕ → Ω → Measure ℂ := fun n => Classical.choose (hex n)
  have hν (n : ℕ) : IsLQGMeasureOfField P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hcirc (ν n) :=
    Classical.choose_spec (hex n)
  have hνall : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLQGLimit γ
      (fieldCircleAverage (lqgQ γ - 1 / ((n : ℝ) + 1)) (hcirc ω)) (ν n ω) :=
    ae_all_iff.mpr hν
  have hcall : ∀ᵐ ω ∂P, ∀ n k : ℕ, Continuous
      (fieldCircleAverage (lqgQ γ - 1 / ((n : ℝ) + 1)) (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k =>
      hG.ae_continuous_fieldCircleAverage _ (dyadicScale_pos k)))
  filter_upwards [hνall, hcall] with ω hνall hcall α hα
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hα)
  have hαn : α ≤ lqgQ γ - 1 / ((n : ℝ) + 1) := by linarith
  exact ⟨(ν n ω).withDensity (fun z => ENNReal.ofReal
      (‖z‖ ^ (γ * ((lqgQ γ - 1 / ((n : ℝ) + 1)) - α)))),
    isLQGLimit_of_weaker_singularity hγ.le hαn (hcirc ω) (hνall n) (hcall n)⟩

/-- The Section 6 conclusions follow from the explicit staged whole-plane
mass, affine and coordinate-change inputs, and countably many existence
inputs approaching the Seiberg bound. -/
theorem section6_of_cofinal_existence_alone
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (n : ℕ),
      LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} := by
  apply section6_of_cofinal_existence hDG hAff hCC ?_ hE
  intro Ω _ P γ hC hcirc
  exact lqgMeasureExistence_of_cofinal P γ 0 hC hcirc (hE Ω P γ hC hcirc)

end HarmonicBalls.Section6
