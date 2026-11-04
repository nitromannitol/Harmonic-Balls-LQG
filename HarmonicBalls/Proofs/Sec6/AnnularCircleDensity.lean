import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal

/-! # Annular approximations for centered circle averages

The annular density difference is supported around both circles, including
when the reference circle is not centered at the origin. The imported Section 8
argument uses Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Real
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- Difference of normalized circle densities with an arbitrary reference center. -/
noncomputable def annularCircleDensityDifference (r η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (z a : ℂ) (n : ℕ) (x : ℂ) : ℝ :=
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x -
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ a x

/-- The difference of normalized annular densities is a local zero-integral
 test function. The two circles need a common local buffer. -/
theorem annularCircleDensity_normalized_difference_test {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) (z a : ℂ) (U : Set ℂ)
    (hz : closedBall z (r + η) ⊆ U) (h0 : closedBall a (r + η) ⊆ U) :
    let m := ∫ x, circleDensity r δ hδ 0 x
    let φ := fun x => m⁻¹ * circleDensity r δ hδ z x - m⁻¹ * circleDensity r δ hδ a x
    IsTestFunction U φ ∧ ∫ x, φ x = 0 := by
  dsimp only
  let m := ∫ x, circleDensity r δ hδ 0 x
  have hztest := circleDensity_isTestFunction hr hδ hwidth z U hz
  have h0test := circleDensity_isTestFunction hr hδ hwidth a U h0
  constructor
  · simpa only [sub_eq_add_neg, neg_mul] using
      hztest.const_mul_add_const_mul h0test m⁻¹ (-m⁻¹)
  · have hzi : Integrable (circleDensity r δ hδ z) volume := (circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)
    have h0i : Integrable (circleDensity r δ hδ a) volume := (circleDensity_contDiff r δ hδ a).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ a)
    rw [integral_sub (hzi.const_mul _) (h0i.const_mul _), integral_const_mul,
      integral_const_mul, circleDensity_integral_eq r δ hδ z, circleDensity_integral_eq r δ hδ a, sub_self]


/-- The covariance of an annular density difference with a circle converges
to the difference of circle covariances. -/
theorem annularCircleDensityDifference_circle_covariance_tendsto {r η s : ℝ}
    (hr : 0 < r) (hη : 0 < η) (hs : 0 < s) (z a w : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov (.pairing (annularCircleDensityDifference r η hr hη z a n))
      (.circle s w)) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle s w) -
        wholePlaneGFFCov (.circle r a) (.circle s w))) := by
  have ht := (circleDensity_circle_covariance_tendsto hr hη hs z w).sub
    (circleDensity_circle_covariance_tendsto hr hη hs a w)
  apply ht.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let m : ℝ := (∫ y, circleDensity r δ hδ 0 y)⁻¹
  let f : ℂ → ℝ := fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s
  have hf : Continuous f := continuous_circleAverage_wholePlaneCov hs w
  have hi (v : ℂ) : Integrable (fun x => m * circleDensity r δ hδ v x * f x) := by
    apply ((continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous).mul hf).integrable_of_hasCompactSupport
    exact (circleDensity_hasCompactSupport hr.le hδ v).mul_left.mul_right
  symm
  change (∫ x, (m * circleDensity r δ hδ z x - m * circleDensity r δ hδ a x) * f x) =
    (∫ x, m * circleDensity r δ hδ z x * f x) -
      ∫ x, m * circleDensity r δ hδ a x * f x
  simp_rw [sub_mul]
  exact integral_sub (hi z) (hi a)


/-- The self-covariance of the signed annular approximation converges to that
of the corresponding difference of circle averages. -/
theorem IsWholePlaneGFF.annularCircleDensityDifference_self_covariance_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z a : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov
      (.pairing (annularCircleDensityDifference r η hr hη z a n))
      (.pairing (annularCircleDensityDifference r η hr hη z a n))) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r a) (.circle r a) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r a))) := by
  have hsym : wholePlaneGFFCov (.circle r a) (.circle r z) =
      wholePlaneGFFCov (.circle r z) (.circle r a) := by
    have h₁ := hGFF.covariance_eq (.circle r a) (.circle r z) hr hr
    have h₂ := hGFF.covariance_eq (.circle r z) (.circle r a) hr hr
    simp only [GFFObservable.eval] at h₁ h₂
    rw [← h₁, ← h₂, covariance_comm]
  have hlim := (((circleDensity_pairing_covariance_tendsto hr hη z z).sub
    (circleDensity_pairing_covariance_tendsto hr hη a z)).sub
    (circleDensity_pairing_covariance_tendsto hr hη z a)).add
    (circleDensity_pairing_covariance_tendsto hr hη a a)
  have heq : wholePlaneGFFCov (.circle r z) (.circle r z) -
      wholePlaneGFFCov (.circle r z) (.circle r a) -
      wholePlaneGFFCov (.circle r a) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) =
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r a) := by
    rw [hsym]
    ring
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let g (v : ℂ) : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ v x
  have hg (v : ℂ) : Continuous (g v) :=
    continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous
  have hgc (v : ℂ) : HasCompactSupport (g v) :=
    (circleDensity_hasCompactSupport hr.le hδ v).mul_left
  have hgm (v : ℂ) : ∫ x, g v x = 1 := circleDensity_normalized_integral hr.le hδ v
  exact (wholePlaneGFFCov_pairing_sub_self (hg z) (hgc z) (hgm z)
    (hg a) (hgc a) (hgm a)).symm


/-- Once the self-covariance of the annular difference converges, all
remaining terms in the local circle approximation error cancel. -/
theorem IsWholePlaneGFF.annularCircleDensityDifference_error_tendsto_of_self
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z a : ℂ)
    (hself : Tendsto (fun n => wholePlaneGFFCov
      (.pairing (annularCircleDensityDifference r η hr hη z a n))
      (.pairing (annularCircleDensityDifference r η hr hη z a n))) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r a) (.circle r a) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r a)))) :
    Tendsto (fun n =>
      wholePlaneGFFCov (.pairing (annularCircleDensityDifference r η hr hη z a n))
        (.pairing (annularCircleDensityDifference r η hr hη z a n)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r a) -
      2 * wholePlaneGFFCov (.pairing (annularCircleDensityDifference r η hr hη z a n)) (.circle r z) +
      2 * wholePlaneGFFCov (.pairing (annularCircleDensityDifference r η hr hη z a n)) (.circle r a))
      atTop (𝓝 0) := by
  have hz := annularCircleDensityDifference_circle_covariance_tendsto hr hη hr z a z
  have h0 := annularCircleDensityDifference_circle_covariance_tendsto hr hη hr z a a
  have hsym : wholePlaneGFFCov (.circle r a) (.circle r z) =
      wholePlaneGFFCov (.circle r z) (.circle r a) := by
    have h₁ := hGFF.covariance_eq (.circle r a) (.circle r z) hr hr
    have h₂ := hGFF.covariance_eq (.circle r z) (.circle r a) hr hr
    simp only [GFFObservable.eval] at h₁ h₂
    rw [← h₁, ← h₂, covariance_comm]
  have hlimit := (((((hself.add (tendsto_const_nhds
    (x := wholePlaneGFFCov (.circle r z) (.circle r z)))).add (tendsto_const_nhds
    (x := wholePlaneGFFCov (.circle r a) (.circle r a)))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_const_nhds
      (x := wholePlaneGFFCov (.circle r z) (.circle r a))))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hz)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).mul h0))
  have heq : (wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r a)) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r a) -
      2 * (wholePlaneGFFCov (.circle r z) (.circle r z) -
        wholePlaneGFFCov (.circle r a) (.circle r z)) +
      2 * (wholePlaneGFFCov (.circle r z) (.circle r a) -
        wholePlaneGFFCov (.circle r a) (.circle r a)) = 0 := by
    rw [hsym]
    ring
  simpa only [heq] using hlimit


/-- The centered circle-minus-pairing variance is given by its six kernel
covariances. -/
theorem IsWholePlaneGFF.variance_pairing_sub_annular_circle_difference
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z a : ℂ)
    (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    variance (fun ω => hC ω φ - (hcirc ω r z - hcirc ω r a)) P =
      wholePlaneGFFCov (.pairing φ) (.pairing φ) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r a) (.circle r a) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r a) -
      2 * wholePlaneGFFCov (.pairing φ) (.circle r z) +
      2 * wholePlaneGFFCov (.pairing φ) (.circle r a) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have h0 : MemLp (fun ω => hcirc ω r a) 2 P := (hGFF.hasGaussianLaw_circle hr a).memLp (by simp)
  change variance ((fun ω => hC ω φ) - ((fun ω => hcirc ω r z) -
    (fun ω => hcirc ω r a))) P = _
  rw [variance_sub hp (hz.sub h0), variance_sub hz h0,
    covariance_sub_right hp hz h0]
  rw [← covariance_self hp.aemeasurable, ← covariance_self hz.aemeasurable,
    ← covariance_self h0.aemeasurable]
  have hpp := hGFF.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  have hzz := hGFF.covariance_eq (.circle r z) (.circle r z) hr hr
  have h00 := hGFF.covariance_eq (.circle r a) (.circle r a) hr hr
  have hz0 := hGFF.covariance_eq (.circle r z) (.circle r a) hr hr
  have hpz := hGFF.covariance_eq (.pairing φ) (.circle r z) hφ hr
  have hp0 := hGFF.covariance_eq (.pairing φ) (.circle r a) hφ hr
  simp only [GFFObservable.eval] at hpp hzz h00 hz0 hpz hp0
  rw [hpp, hzz, h00, hz0, hpz, hp0]
  ring


/-- Vanishing covariance-kernel error for local zero-integral tests gives a
joint local version of the centered circle-average field. -/
theorem IsWholePlaneGFF.exists_joint_annular_centered_circle_version_of_covariance_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (U : Set ℂ) (hU : IsOpen U) (a : ℂ)
    (happrox : ∀ z, closedBall z r ⊆ U → ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction (U) (φ n) ∧ ∫ x, φ n x = 0) ∧
      Tendsto (fun n =>
        wholePlaneGFFCov (.pairing (φ n)) (.pairing (φ n)) +
        wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r a) (.circle r a) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r a) -
        2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r z) +
        2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r a)) atTop (𝓝 0)) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (U)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ U →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r a := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  apply exists_joint_local_version_of_pointwise
    (Section6.fieldSigmaAlgebraModConst α₀ hC U)
    (isOpen_centers_closedBall_subset r hU)
  · filter_upwards [hGFF.ae_continuous_fieldCircleAverage α₀ hr] with ω hω
    exact hω.sub continuous_const
  intro z hz
  obtain ⟨φ, hφ, hkernel⟩ := happrox z hz
  have htest (n : ℕ) : IsTestFunction univ (φ n) :=
    ⟨(hφ n).1.1, (hφ n).1.2.1, subset_univ _⟩
  have hp (n : ℕ) : MemLp (fun ω => hC ω (φ n)) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (φ n), htest n⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hzLp : MemLp (fun ω => hcirc ω r z) 2 P :=
    (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have h0Lp : MemLp (fun ω => hcirc ω r a) 2 P :=
    (hGFF.hasGaussianLaw_circle hr a).memLp (by simp)
  have hm : ∀ n, ∫ ω, (hC ω (φ n) - (hcirc ω r z - hcirc ω r a)) ∂P = 0 := by
    intro n
    have hp0 := hGFF.integral_eq_zero (.pairing (φ n)) (htest n)
    have hz0 := hGFF.integral_eq_zero (.circle r z) hr
    have h00 := hGFF.integral_eq_zero (.circle r a) hr
    simp only [GFFObservable.eval] at hp0 hz0 h00
    have hxy : Integrable (fun ω => hcirc ω r z - hcirc ω r a) P :=
      (hzLp.sub h0Lp).integrable (by simp)
    rw [integral_sub ((hp n).integrable (by simp)) hxy,
      integral_sub (hzLp.integrable (by simp)) (h0Lp.integrable (by simp)), hp0, hz0, h00]
    ring
  have hvar : Tendsto (fun n => variance
      (fun ω => hC ω (φ n) - (hcirc ω r z - hcirc ω r a)) P) atTop (𝓝 0) := by
    convert hkernel using 1
    funext n
    exact hGFF.variance_pairing_sub_annular_circle_difference hr z a (φ n) (htest n)
  have hprob : TendstoInMeasure P (fun n ω => hC ω (φ n)) atTop
      (fun ω => hcirc ω r z - hcirc ω r a) :=
    tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
      (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar
  have hpair (n : ℕ) : @Measurable Ω ℝ
      (Section6.fieldSigmaAlgebraModConst α₀ hC (U)) _ (fun ω => hC ω (φ n)) := by
    have h := measurable_fieldPairing_modConst α₀ hC (U) (φ n) (hφ n)
    have h' := h.add_const (α₀ * ∫ x, φ n x * Real.log ‖x‖)
    simpa only [fieldPairing, sub_add_cancel] using h'
  obtain ⟨g, hg, hge⟩ := exists_measurable_version_of_tendstoInMeasure
    (Section6.fieldSigmaAlgebraModConst α₀ hC (U)) _ _ hpair hprob
  refine ⟨fun ω => g ω - α₀ * (Real.circleAverage (fun x => Real.log ‖x‖) z r -
    Real.circleAverage (fun x => Real.log ‖x‖) a r), hg.sub_const _, ?_⟩
  filter_upwards [hge] with ω hω
  dsimp only [fieldCircleAverage]
  rw [← hω]
  ring

/-- Circle averages centered at a reference circle in an open set have a
jointly measurable version in the local field sigma algebra modulo constants. -/
theorem IsWholePlaneGFF.exists_joint_annular_centered_circle_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (ha : closedBall a r ⊆ U) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC U).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ U →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r a := by
  apply hGFF.exists_joint_annular_centered_circle_version_of_covariance_limit hr U hU a
  intro z hz
  obtain ⟨ηz, hηz, hz'⟩ := exists_enlarged_closedBall_subset_open hr.le z hU hz
  obtain ⟨ηa, hηa, ha'⟩ := exists_enlarged_closedBall_subset_open hr.le a hU ha
  let η := min ηz ηa
  have hη : 0 < η := lt_min hηz hηa
  have hz'' : closedBall z (r + η) ⊆ U :=
    (closedBall_subset_closedBall (by dsimp [η]; linarith [min_le_left ηz ηa])).trans hz'
  have ha'' : closedBall a (r + η) ⊆ U :=
    (closedBall_subset_closedBall (by dsimp [η]; linarith [min_le_right ηz ηa])).trans ha'
  refine ⟨annularCircleDensityDifference r η hr hη z a, ?_, ?_⟩
  · intro n
    have hwidth : circleDensityWidth r η n ≤ r * η := by
      unfold circleDensityWidth
      apply div_le_self (mul_nonneg hr.le hη.le)
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    change IsTestFunction U (fun x => annularCircleDensityDifference r η hr hη z a n x) ∧ _
    simpa only [annularCircleDensityDifference] using
      (annularCircleDensity_normalized_difference_test hr (circleDensityWidth_pos hr hη n)
        hwidth z a U hz'' ha'')
  · exact hGFF.annularCircleDensityDifference_error_tendsto_of_self hr hη z a
      (hGFF.annularCircleDensityDifference_self_covariance_tendsto hr hη z a)

end HarmonicBalls
