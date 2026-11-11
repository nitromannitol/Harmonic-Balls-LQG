import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Laws of Gaussian processes

The law of a real Gaussian process is determined by its means and
covariances, including for an uncountable index set.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory

/-- Real Gaussian processes with the same means and covariances have the
same joint law. No countability assumption on the index set is needed. -/
theorem gaussian_process_map_eq_of_mean_covariance
    {Ω Ω' T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') (X : T → Ω → ℝ) (Y : T → Ω' → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hXm : ∀ t, Measurable (X t)) (hYm : ∀ t, Measurable (Y t))
    (hmean : ∀ t, (∫ ω, X t ω ∂P) = ∫ ω, Y t ω ∂Q)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q]) :
    P.map (fun ω t => X t ω) = Q.map (fun ω t => Y t ω) := by
  let := hX.isProbabilityMeasure
  let := hY.isProbabilityMeasure
  have hXall : AEMeasurable (fun ω t => X t ω) P := (measurable_pi_iff.mpr hXm).aemeasurable
  have hYall : AEMeasurable (fun ω t => Y t ω) Q := (measurable_pi_iff.mpr hYm).aemeasurable
  apply (isProjectiveLimit_map hXall).unique
  intro I
  have hfinite : P.map (fun ω => I.restrict (X · ω)) =
      Q.map (fun ω => I.restrict (Y · ω)) := by
    apply (MeasurableEquiv.toLp 2 (_ → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
    have := (hX.hasGaussianLaw I).isGaussian_map
    have := (hY.hasGaussianLaw I).isGaussian_map
    apply IsGaussian.ext
    · rw [integral_map, integral_map, integral_map, integral_map]
      · simp only [id_eq]
        rw [ContinuousLinearEquiv.integral_comp_comm, ContinuousLinearEquiv.integral_comp_comm]
        congr 1
        funext i
        rw [eval_integral, eval_integral]
        · exact hmean i
        · exact fun i => (hY.hasGaussianLaw_eval _).integrable
        · exact fun i => (hX.hasGaussianLaw_eval _).integrable
      all_goals first
        | fun_prop
        | exact (measurable_pi_iff.mpr fun i : I => hXm i).aemeasurable
        | exact (measurable_pi_iff.mpr fun i : I => hYm i).aemeasurable
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
        isPosSemidef_covarianceBilin.isSymm fun x => ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      rw [PiLp.coe_symm_continuousLinearEquiv, covarianceBilin_apply_pi, covarianceBilin_apply_pi]
      · congrm ∑ i, ∑ j, _ * ?_
        rw [covariance_map, covariance_map]
        · exact hcov i j
        all_goals first | exact Measurable.aestronglyMeasurable (by fun_prop) | exact .of_eval (fun _ => hX.aemeasurable _) | exact .of_eval (fun _ => hY.aemeasurable _)
      · exact fun i => (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
      · exact fun i => (IsGaussian.hasGaussianLaw_id.eval i).memLp_two
  rw [isProjectiveLimit_map hYall I]
  exact hfinite.symm

/-- Two whole-plane GFF realizations have identical joint laws for every
collection of local test-function pairings, including the same deterministic
logarithmic singularity. -/
theorem wholePlaneGFF_localFieldPairings_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc')
    (α₀ : ℝ) (U : Set ℂ) :
    P.map (localFieldPairings α₀ hC U) = Q.map (localFieldPairings α₀ hC' U) := by
  let o (φ : LocalFieldTest U) : GFFObservable.Admissible :=
    ⟨.pairing φ.1, ⟨φ.2.1, φ.2.2.1, Set.subset_univ _⟩⟩
  let X (φ : LocalFieldTest U) (ω : Ω) := hC ω φ.1
  let Y (φ : LocalFieldTest U) (ω : Ω') := hC' ω φ.1
  have hX : IsGaussianProcess X P := hP.isGaussianProcess.comp_right o
  have hY : IsGaussianProcess Y Q := hQ.isGaussianProcess.comp_right o
  have hXm : ∀ φ, Measurable (X φ) := fun φ => hP.measurable_pairing _ (o φ).2
  have hYm : ∀ φ, Measurable (Y φ) := fun φ => hQ.measurable_pairing _ (o φ).2
  have hmean : ∀ φ, (∫ ω, X φ ω ∂P) = ∫ ω, Y φ ω ∂Q := by
    intro φ
    exact (hP.integral_eq_zero _ (o φ).2).trans (hQ.integral_eq_zero _ (o φ).2).symm
  have hcov : ∀ φ ψ, cov[X φ, X ψ; P] = cov[Y φ, Y ψ; Q] := by
    intro φ ψ
    exact (hP.covariance_eq _ _ (o φ).2 (o ψ).2).trans
      (hQ.covariance_eq _ _ (o φ).2 (o ψ).2).symm
  have heq := gaussian_process_map_eq_of_mean_covariance P Q X Y hX hY hXm hYm hmean hcov
  let F (v : LocalFieldTest U → ℝ) (φ : LocalFieldTest U) :=
    v φ - α₀ * ∫ x, φ.1 x * Real.log ‖x‖
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply φ).sub measurable_const
  have hPX : Measurable (fun ω φ => X φ ω) := measurable_pi_iff.mpr hXm
  have hQY : Measurable (fun ω φ => Y φ ω) := measurable_pi_iff.mpr hYm
  have hmap := congrArg (fun ν : Measure (LocalFieldTest U → ℝ) => ν.map F) heq
  rw [Measure.map_map hF hPX, Measure.map_map hF hQY] at hmap
  exact hmap

/-- On the sigma algebra of a local field, two laws making the same field a
normalized whole-plane GFF agree. -/
theorem wholePlaneGFF_trim_fieldSigmaAlgebra_eq
    {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC hcirc')
    (α₀ : ℝ) (U : Set ℂ) :
    P.trim (hP.fieldSigmaAlgebra_le α₀ U) = Q.trim (hP.fieldSigmaAlgebra_le α₀ U) := by
  have hf : Measurable (localFieldPairings α₀ hC U) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hP.fieldSigmaAlgebra_le α₀ U
  have heq := wholePlaneGFF_localFieldPairings_map_eq hP hQ α₀ U
  apply @Measure.ext Ω (fieldSigmaAlgebra α₀ hC U)
  intro A hA
  have hAc : MeasurableSet[MeasurableSpace.comap (localFieldPairings α₀ hC U)
      inferInstance] A := by
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hAc
  rw [trim_measurableSet_eq _ hA, trim_measurableSet_eq _ hA,
    ← Measure.map_apply hf hB, ← Measure.map_apply hf hB, heq]




end HarmonicBalls
