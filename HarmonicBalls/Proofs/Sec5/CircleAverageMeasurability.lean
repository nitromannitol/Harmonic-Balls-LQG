import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-! # A jointly measurable modification of the circle-average process -/

namespace HarmonicBalls

open MeasureTheory Set Filter ProbabilityTheory

/-- A whole-plane GFF has a modification whose circle averages are continuous
in the spatial variable at every positive radius and jointly measurable in the
spatial variable and the sample point. -/
theorem IsWholePlaneGFF.exists_jointlyMeasurable_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∃ H : Ω → ℝ → ℂ → ℝ,
      (∀ ω r, 0 < r → Continuous (H ω r)) ∧
      (∀ r, 0 < r → Measurable (fun p : ℂ × Ω => H p.2 r p.1)) ∧
      (∀ᵐ ω ∂P, ∀ r z, H ω r z = hcirc ω r z) := by
  classical
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hGFF.ae_continuousOn_circle)
  let H : Ω → ℝ → ℂ → ℝ := fun ω r z => if ω ∈ N then 0 else hcirc ω r z
  have hcont : ∀ ω r, 0 < r → Continuous (H ω r) := by
    intro ω r hr
    by_cases hω : ω ∈ N
    · simpa [H, hω] using (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))
    · have hc : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
          (Ioi 0 ×ˢ univ) := by
        by_contra hnot
        exact hω (hNsub hnot)
      have h := hc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z : ℂ => ⟨hr, mem_univ z⟩)
      simpa [H, hω, Function.comp_def] using h
  have hmeas : ∀ r, 0 < r → Measurable (fun p : ℂ × Ω => H p.2 r p.1) := by
    intro r hr
    change Measurable (Function.uncurry (fun z ω => H ω r z))
    apply measurable_uncurry_of_continuous_of_measurable
    · exact fun ω => hcont ω r hr
    · intro z
      exact Measurable.ite hNmeas measurable_const (hGFF.measurable_circle r z hr)
  refine ⟨H, hcont, hmeas, ?_⟩
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hNnull)
  filter_upwards [hae] with ω hω
  intro r z
  simp [H, hω]

/-- Each dyadic LQG approximation is an almost-everywhere measurable random
measure, including in the presence of a logarithmic singularity. -/
theorem IsWholePlaneGFF.aemeasurable_lqgApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (n : ℕ) :
    AEMeasurable (fun ω => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)) P := by
  obtain ⟨H, _, hmeas, hae⟩ := hGFF.exists_jointlyMeasurable_circleAverage
  have hr := dyadicScale_pos n
  have hH : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale n) p.2) :=
    (hmeas _ hr).comp measurable_swap
  have hfield : Measurable (fun p : Ω × ℂ =>
      fieldCircleAverage α₀ (H p.1) (dyadicScale n) p.2) := by
    simp_rw [fieldCircleAverage_eq _ _ hr]
    exact hH.sub (measurable_const.mul ((measurable_const.max measurable_snd.norm).log))
  have hdensity : Measurable (fun p : Ω × ℂ => ENNReal.ofReal
      (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ *
        fieldCircleAverage α₀ (H p.1) (dyadicScale n) p.2))) :=
    (measurable_const.mul ((measurable_const.mul hfield).exp)).ennreal_ofReal
  have happrox : Measurable (fun ω =>
      lqgApprox γ (fieldCircleAverage α₀ (H ω)) (dyadicScale n)) := by
    apply measurable_withDensity
    exact hdensity
  apply happrox.aemeasurable.congr
  filter_upwards [hae] with ω hω
  have heq : H ω = hcirc ω := by funext r z; exact hω r z
  rw [heq]

/-- The one-point circle-average law is determined by the covariance kernel,
even when the two fields live on different probability spaces. -/
theorem IsWholePlaneGFF.identDistrib_circleAverage
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IdentDistrib (fun ω => hcirc ω r z) (fun ω => hcirc' ω r z) P P' := by
  have hG := h.hasGaussianLaw_circle hr z
  have hG' := h'.hasGaussianLaw_circle hr z
  have hm : ∫ ω, hcirc ω r z ∂P = 0 := h.integral_eq_zero (.circle r z) hr
  have hm' : ∫ ω, hcirc' ω r z ∂P' = 0 := h'.integral_eq_zero (.circle r z) hr
  have hv : Var[fun ω => hcirc ω r z; P] = Var[fun ω => hcirc' ω r z; P'] := by
    rw [← covariance_self hG.aemeasurable, ← covariance_self hG'.aemeasurable]
    exact (h.covariance_eq (.circle r z) (.circle r z) hr hr).trans
      (h'.covariance_eq (.circle r z) (.circle r z) hr hr).symm
  refine ⟨hG.aemeasurable, hG'.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hG'.map_eq_gaussianReal, hm, hm', hv]

/-- The one-point law also agrees after adding the same logarithmic singularity. -/
theorem IsWholePlaneGFF.identDistrib_fieldCircleAverage
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (α₀ : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IdentDistrib (fun ω => fieldCircleAverage α₀ (hcirc ω) r z)
      (fun ω => fieldCircleAverage α₀ (hcirc' ω) r z) P P' := by
  simp_rw [fieldCircleAverage_eq _ _ hr]
  exact (h.identDistrib_circleAverage h' hr z).sub_const (α₀ * Real.log (max r ‖z‖))

/-- Affine invariance gives the one-point law of every circle average of the
normalized rescaled field. -/
theorem IsWholePlaneGFF.identDistrib_normalizedScale_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    {k r : ℝ} (hk : 0 < k) (hr : 0 < r) (z : ℂ) :
    IdentDistrib (fun ω => hcirc ω r z)
      (fun ω => hcirc ω (k * r) (k • z) - hcirc ω k 0) P P := by
  have hscaled := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hident := h.identDistrib_circleAverage hscaled hr z
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, add_zero,
    Complex.real_smul] using hident

end HarmonicBalls
