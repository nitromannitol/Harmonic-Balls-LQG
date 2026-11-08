import Mathlib

/-! # Route (A), Palm identity: the finite-dimensional Gaussian exponential tilt

Let `Y` be a centred Gaussian variable of variance `v ≠ 0`, let `X_1, …, X_k` be real random variables such that
`(X, Y)` is a Gaussian vector, and let `a_j = Cov(X_j, Y)`. Then for every bounded continuous `ψ : ℝ^k → ℝ`,
`E[ψ(X) exp(γ Y - γ² v / 2)] = E[ψ(X + γ a)]`: the exponential tilt by `Y` shifts the law of `X` by `γ a`.
This is the finite-dimensional tilt of r10 `l:r9-marked` (`sec11-proof-r10.tex`, "Retaining the marked point in
Gaussian tilting", lines 2681-2700).

The covariance matrix of `X` is never inverted: the proof writes `X = W + (a/v) Y` with `W` independent of `Y`
(Mathlib `HasGaussianLaw.indepFun_of_covariance_eval`, since the covariances of `W` with `Y` vanish), and then tilts
the one-dimensional law of `Y` alone. Degenerate covariance matrices of `X` are therefore covered.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HarmonicBalls

/-- The tilting density `y ↦ exp(γ y - γ² v / 2)`, as an `ℝ≥0∞`-valued function, is measurable. -/
theorem measurable_ofReal_exp_tilt (γ : ℝ) (v : ℝ≥0) :
    Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (γ * y - γ ^ 2 * v / 2))) := by
  refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp ?_)
  exact (measurable_id.const_mul γ).sub measurable_const

/-- The exponential tilt of the centred Gaussian `N(0, v)` by `exp(γ y - γ² v / 2)` is the Gaussian `N(γ v, v)`. -/
theorem gaussianReal_withDensity_exp_tilt (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ) :
    (gaussianReal 0 v).withDensity (fun y => ENNReal.ofReal (Real.exp (γ * y - γ ^ 2 * v / 2))) =
      gaussianReal (γ * v) v := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (measurable_gaussianPDF 0 v) (measurable_ofReal_exp_tilt γ v)]
  congr 1
  funext y
  simp only [Pi.mul_apply]
  unfold gaussianPDF
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v y)]
  congr 1
  unfold gaussianPDFReal
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- One-dimensional exponential tilt: for `Y ~ N(0, v)` and a bounded measurable `f`,
`E[exp(γ Y - γ² v / 2) f(Y)] = E[f(Y + γ v)]`. -/
theorem integral_gaussianReal_exp_tilt (v : ℝ≥0) (hv : v ≠ 0) (γ : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ y, Real.exp (γ * y - γ ^ 2 * v / 2) * f y ∂(gaussianReal 0 v) =
      ∫ y, f (y + γ * v) ∂(gaussianReal 0 v) := by
  have hsh : (gaussianReal 0 v).map (· + γ * v) = gaussianReal (γ * v) v := by
    have h := gaussianReal_map_add_const (μ := 0) (v := v) (γ * v)
    rwa [zero_add] at h
  have hRHS : ∫ y, f (y + γ * v) ∂(gaussianReal 0 v) = ∫ y, f y ∂(gaussianReal (γ * v) v) := by
    rw [← hsh, integral_map (measurable_add_const _).aemeasurable hf.aestronglyMeasurable]
  have hLHS : ∫ y, Real.exp (γ * y - γ ^ 2 * v / 2) * f y ∂(gaussianReal 0 v) =
      ∫ y, f y ∂(gaussianReal (γ * v) v) := by
    rw [← gaussianReal_withDensity_exp_tilt v hv γ,
      integral_withDensity_eq_integral_toReal_smul₀ (measurable_ofReal_exp_tilt γ v).aemeasurable]
    · congr 1
      funext y
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    · exact ae_of_all _ fun y => ENNReal.ofReal_lt_top
  rw [hLHS, hRHS]

/-- **Finite-dimensional Gaussian exponential tilt.** Let `Y` be centred Gaussian with variance `v ≠ 0`, let `X_j`
be real random variables such that `(X, Y)` is a Gaussian vector, and let `a_j = Cov(X_j, Y)`. Then for every
bounded continuous `ψ : ℝ^k → ℝ`, `E[ψ(X) exp(γ Y - γ² v / 2)] = E[ψ(X + γ a)]`. The covariance matrix of `X`
need not be invertible. -/
theorem integral_gaussian_exp_tilt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (X : Fin k → Ω → ℝ) (Y : Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hYm : Measurable Y)
    (v : ℝ≥0) (hv : v ≠ 0) (hY : HasLaw Y (gaussianReal 0 v) P)
    (hG : HasGaussianLaw (fun ω => ((fun j => X j ω), Y ω)) P)
    (a : Fin k → ℝ) (ha : ∀ j, cov[X j, Y; P] = a j) (γ : ℝ)
    (ψ : (Fin k → ℝ) → ℝ) (hψ : Continuous ψ) (C : ℝ) (hψC : ∀ x, |ψ x| ≤ C) :
    ∫ ω, ψ (fun j => X j ω) * Real.exp (γ * Y ω - γ ^ 2 * v / 2) ∂P =
      ∫ ω, ψ (fun j => X j ω + γ * a j) ∂P := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  -- the coefficients `c_j = a_j / v` of the decomposition `X = W + c Y`
  set c : Fin k → ℝ := fun j => a j / (v : ℝ) with hc_def
  have hcv : ∀ j, c j * (v : ℝ) = a j := fun j => div_mul_cancel₀ (a j) hv'
  -- second moments and the variance of `Y`
  have hXL2 : ∀ j, MemLp (X j) 2 P := fun j =>
    (hG.map ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ))).memLp_two
  have hYL2 : MemLp Y 2 P := (hG.map (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)).memLp_two
  have hYY : cov[Y, Y; P] = (v : ℝ) := by
    rw [covariance_self hYm.aemeasurable, hY.variance_eq, variance_id_gaussianReal]
  -- the Gaussian vector `((W_j)_j, Y)` with `W_j = X_j - c_j Y` is a linear image of `((X_j)_j, Y)`
  let L : ((Fin k → ℝ) × ℝ) →L[ℝ] ((Fin k → ℝ) × (Unit → ℝ)) :=
    (ContinuousLinearMap.pi fun j : Fin k =>
        (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ) -
          c j • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).prod
      (ContinuousLinearMap.pi fun _ : Unit => ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)
  have hWY : HasGaussianLaw (fun ω => ((fun j => X j ω - c j * Y ω), (fun _ : Unit => Y ω))) P :=
    hG.map L
  have hcov : ∀ j : Fin k, cov[fun ω => X j ω - c j * Y ω, fun ω => Y ω; P] = 0 := by
    intro j
    have key : cov[X j - (fun ω => c j * Y ω), Y; P] = 0 := by
      rw [covariance_sub_left (hXL2 j) (hYL2.const_mul (c j)) hYL2, covariance_const_mul_left, hYY, ha j]
      linarith [hcv j]
    exact key
  -- independence of `W` and `Y` from the vanishing covariances
  have hIndepFam : IndepFun (fun ω j => X j ω - c j * Y ω) (fun ω (_ : Unit) => Y ω) P :=
    HasGaussianLaw.indepFun_of_covariance_eval (X := fun j ω => X j ω - c j * Y ω)
      (Y := fun (_ : Unit) ω => Y ω) hWY (fun j _ => hcov j)
  have hIndep : IndepFun (fun ω j => X j ω - c j * Y ω) (fun ω => Y ω) P :=
    hIndepFam.comp measurable_id (measurable_pi_apply ())
  have hWm : Measurable (fun ω j => X j ω - c j * Y ω) :=
    Measurable.of_eval fun j => (hX j).sub (hYm.const_mul (c j))
  have hZm0 : Measurable (fun ω => ((fun j => X j ω - c j * Y ω), Y ω)) := hWm.prodMk hYm
  have hjoint : P.map (fun ω => ((fun j => X j ω - c j * Y ω), Y ω)) =
      (P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v) := by
    rw [← hY.map_eq]
    exact (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hYm.aemeasurable).1 hIndep
  -- the integrands on `ℝ^k × ℝ`
  set Z : Ω → (Fin k → ℝ) × ℝ := fun ω => ((fun j => X j ω - c j * Y ω), Y ω) with hZdef
  set F : (Fin k → ℝ) × ℝ → ℝ := fun p =>
    ψ (fun j => p.1 j + c j * p.2) * Real.exp (γ * p.2 - γ ^ 2 * v / 2) with hFdef
  set G : (Fin k → ℝ) × ℝ → ℝ := fun p => ψ (fun j => (p.1 j + γ * a j) + c j * p.2) with hGdef
  have hFc : Continuous F := by
    rw [hFdef]
    fun_prop
  have hGc : Continuous G := by
    rw [hGdef]
    fun_prop
  have hFb : ∀ p, ‖F p‖ ≤ C * Real.exp (γ * p.2 - γ ^ 2 * v / 2) := by
    intro p
    simp only [hFdef]
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hψC _) (Real.exp_nonneg _)
  have hEint : Integrable (fun y : ℝ => Real.exp (γ * y - γ ^ 2 * v / 2)) (gaussianReal 0 v) := by
    have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := v) γ).const_mul
      (Real.exp (-(γ ^ 2 * v / 2)))
    refine h.congr (ae_of_all _ fun y => ?_)
    show Real.exp (-(γ ^ 2 * v / 2)) * Real.exp (γ * y) = Real.exp (γ * y - γ ^ 2 * v / 2)
    rw [← Real.exp_add]
    congr 1
    ring
  have hBint : Integrable (fun p : (Fin k → ℝ) × ℝ => C * Real.exp (γ * p.2 - γ ^ 2 * v / 2))
      ((P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v)) :=
    (hEint.const_mul C).comp_snd _
  have hFint : Integrable F ((P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v)) :=
    hBint.mono' hFc.measurable.aestronglyMeasurable (ae_of_all _ hFb)
  have hGint : Integrable G ((P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v)) := by
    refine (integrable_const C).mono' hGc.measurable.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [hGdef]
    rw [Real.norm_eq_abs]
    exact hψC _
  -- transfer to the product law of `(W, Y)`
  have hmapF : ∫ ω, F (Z ω) ∂P =
      ∫ p, F p ∂((P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v)) := by
    rw [← hjoint, integral_map hZm0.aemeasurable hFc.measurable.aestronglyMeasurable]
  have hmapG : ∫ ω, G (Z ω) ∂P =
      ∫ p, G p ∂((P.map (fun ω j => X j ω - c j * Y ω)).prod (gaussianReal 0 v)) := by
    rw [← hjoint, integral_map hZm0.aemeasurable hGc.measurable.aestronglyMeasurable]
  have hLHS : ∫ ω, ψ (fun j => X j ω) * Real.exp (γ * Y ω - γ ^ 2 * v / 2) ∂P = ∫ ω, F (Z ω) ∂P := by
    congr 1
    funext ω
    simp only [hFdef, hZdef, sub_add_cancel]
  have hRHS : ∫ ω, ψ (fun j => X j ω + γ * a j) ∂P = ∫ ω, G (Z ω) ∂P := by
    congr 1
    funext ω
    simp only [hGdef, hZdef]
    congr 1
    funext j
    ring
  -- the fibrewise identity: the one-dimensional tilt in `y`, with `c_j γ v = γ a_j`
  have hinner : ∀ w : Fin k → ℝ,
      ∫ y, F (w, y) ∂(gaussianReal 0 v) = ∫ y, G (w, y) ∂(gaussianReal 0 v) := by
    intro w
    have hcont : Continuous (fun y : ℝ => fun j => w j + c j * y) := by
      fun_prop
    have hfm : Measurable (fun y : ℝ => ψ (fun j => w j + c j * y)) := (hψ.comp hcont).measurable
    have h1 := integral_gaussianReal_exp_tilt v hv γ (fun y => ψ (fun j => w j + c j * y)) hfm
    have e1 : ∀ y, F (w, y) = Real.exp (γ * y - γ ^ 2 * v / 2) * ψ (fun j => w j + c j * y) := by
      intro y
      simp only [hFdef]
      ring
    have e2 : ∀ y, G (w, y) = ψ (fun j => w j + c j * (y + γ * v)) := by
      intro y
      simp only [hGdef]
      congr 1
      funext j
      linear_combination (-γ) * hcv j
    simp only [e1, e2]
    exact h1
  rw [hLHS, hRHS, hmapF, hmapG, integral_prod F hFint, integral_prod G hGint]
  congr 1
  funext w
  exact hinner w

end HarmonicBalls

end
