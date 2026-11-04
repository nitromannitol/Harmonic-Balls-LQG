import HarmonicBalls.Proofs.Sec5.CircleAverageMeasurability

/-! # Finite-dimensional laws of the circle-average process -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory WithLp

/-- Finite Gaussian vectors with equal means and pairwise covariances have the
same law, including on different probability spaces. -/
theorem identDistrib_gaussian_vector_of_mean_covariance
    {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω => (X · ω)) P)
    (hY : HasGaussianLaw (fun ω => (Y · ω)) P')
    (hmean : ∀ i, ∫ ω, X i ω ∂P = ∫ ω, Y i ω ∂P')
    (hcov : ∀ i j, cov[X i, X j; P] = cov[Y i, Y j; P']) :
    IdentDistrib (fun ω => (X · ω)) (fun ω => (Y · ω)) P P' := by
  let _ := hX.isProbabilityMeasure
  let _ := hY.isProbabilityMeasure
  have hXL := hX.toLp_pi 2
  have hYL := hY.toLp_pi 2
  have hmap : P.map (fun ω => toLp 2 (X · ω)) = P'.map (fun ω => toLp 2 (Y · ω)) := by
    let _ := hXL.isGaussian_map
    let _ := hYL.isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map hXL.aemeasurable aestronglyMeasurable_id,
        integral_map hYL.aemeasurable aestronglyMeasurable_id]
      ext i
      rw [eval_integral_piLp (fun i => (hX.eval i).integrable),
        eval_integral_piLp (fun i => (hY.eval i).integrable)]
      exact hmean i
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      change covarianceBilin (P.map (fun ω => toLp 2 (X · ω)))
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) =
        covarianceBilin (P'.map (fun ω => toLp 2 (Y · ω)))
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)
      rw [covarianceBilin_apply_basisFun (fun i => (hX.eval i).memLp_two),
        covarianceBilin_apply_basisFun (fun i => (hY.eval i).memLp_two)]
      exact hcov i j
  have h := (IdentDistrib.mk hXL.aemeasurable hYL.aemeasurable hmap).comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable
  simpa only [Function.comp_def, MeasurableEquiv.coe_toLp_symm, ofLp_toLp] using h

/-- Any finite family of admissible observables has the same joint law for
two whole-plane GFFs. -/
theorem IsWholePlaneGFF.identDistrib_finite_observables
    {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (v : ι → GFFObservable.Admissible) :
    IdentDistrib (fun ω i => (v i).1.eval (hC ω) (hcirc ω))
      (fun ω i => (v i).1.eval (hC' ω) (hcirc' ω)) P P' := by
  classical
  let X : ι → Ω → ℝ := fun i ω => (v i).1.eval (hC ω) (hcirc ω)
  let Y : ι → Ω' → ℝ := fun i ω => (v i).1.eval (hC' ω) (hcirc' ω)
  have hX : HasGaussianLaw (fun ω => (X · ω)) P := by
    have hG := (h.isGaussianProcess.comp_right v).hasGaussianLaw Finset.univ
    have hL := hG.map (ContinuousLinearMap.pi fun i : ι =>
      ContinuousLinearMap.proj (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset ι)))
    convert hL using 1
    funext ω i
    rfl
  have hY : HasGaussianLaw (fun ω => (Y · ω)) P' := by
    have hG := (h'.isGaussianProcess.comp_right v).hasGaussianLaw Finset.univ
    have hL := hG.map (ContinuousLinearMap.pi fun i : ι =>
      ContinuousLinearMap.proj (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset ι)))
    convert hL using 1
    funext ω i
    rfl
  apply identDistrib_gaussian_vector_of_mean_covariance hX hY
  · intro i
    change (∫ ω, (v i).1.eval (hC ω) (hcirc ω) ∂P) =
      (∫ ω, (v i).1.eval (hC' ω) (hcirc' ω) ∂P')
    rw [h.integral_eq_zero (v i).1 (v i).2, h'.integral_eq_zero (v i).1 (v i).2]
  · intro i j
    change cov[(fun ω => (v i).1.eval (hC ω) (hcirc ω)),
        (fun ω => (v j).1.eval (hC ω) (hcirc ω)); P] =
      cov[(fun ω => (v i).1.eval (hC' ω) (hcirc' ω)),
        (fun ω => (v j).1.eval (hC' ω) (hcirc' ω)); P']
    rw [h.covariance_eq (v i).1 (v j).1 (v i).2 (v j).2,
      h'.covariance_eq (v i).1 (v j).1 (v i).2 (v j).2]

/-- On a common probability space, the joint law of all admissible observables
is determined by the whole-plane GFF specification. -/
theorem IsWholePlaneGFF.identDistrib_observables
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc') :
    IdentDistrib (fun (ω : Ω) (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω))
      (fun (ω : Ω) (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) P P := by
  let _ := h.isGaussianProcess.isProbabilityMeasure
  have hm : ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → Measurable
        (fun (ω : Ω) (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) := by
    intro hC hcirc hh
    apply Measurable.of_eval
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact hh.measurable_pairing φ ho
    | circle r z => exact hh.measurable_circle r z ho
  apply (identDistrib_iff_forall_finset_identDistrib
    (hm hC hcirc h).aemeasurable (hm hC' hcirc' h').aemeasurable).2
  intro I
  exact h.identDistrib_finite_observables h' Subtype.val

/-- The normalized rescaling of a whole-plane GFF has the same joint law for
all positive-radius circle averages, assuming affine invariance. -/
theorem IsWholePlaneGFF.identDistrib_normalizedScale_circleProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) => hcirc ω p.1 p.2)
      (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
        hcirc ω (k * p.1) (k • p.2) - hcirc ω k 0) P P := by
  let v : {r : ℝ // 0 < r} × ℂ → GFFObservable.Admissible :=
    fun p => ⟨.circle p.1 p.2, p.1.2⟩
  have hv : Measurable (fun f : GFFObservable.Admissible → ℝ => fun p => f (v p)) :=
    Measurable.of_eval fun p => measurable_pi_apply (v p)
  have hs := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hdist := (h.identDistrib_observables hs).comp hv
  simpa only [Function.comp_def, v, GFFObservable.eval, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hk, add_zero, Complex.real_smul] using hdist

/-- The same joint circle-average law holds after adding the logarithmic
singularity used to define the LQG measure. -/
theorem IsWholePlaneGFF.identDistrib_normalizedScale_fieldCircleProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (α₀ : ℝ)
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
        fieldCircleAverage α₀ (hcirc ω) p.1 p.2)
      (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
        fieldCircleAverage α₀ (fun r z => hcirc ω (k * r) (k • z) - hcirc ω k 0) p.1 p.2)
      P P := by
  let F : ({r : ℝ // 0 < r} × ℂ → ℝ) → ({r : ℝ // 0 < r} × ℂ → ℝ) :=
    fun f p => f p - α₀ * Real.log (max p.1 ‖p.2‖)
  have hF : Measurable F := Measurable.of_eval fun p =>
    (measurable_pi_apply p).sub measurable_const
  have hdist := (h.identDistrib_normalizedScale_circleProcess hAff hk).comp hF
  convert hdist using 1 <;> funext ω p <;>
    exact fieldCircleAverage_eq α₀ _ p.1.property p.2

end HarmonicBalls
