import HarmonicBalls.Defs.GFF

/-!
# A.s. homogeneity of the whole-plane GFF pairing for a fixed scalar and test function (fp-S11v, operator note 01:44 UTC)

Option (b) of `notes/fp-gaps/CHATGPT-n1-hAff-hhom.md` §3: `IsWholePlaneGFF` has no a.s. linearity in the test function
simultaneously for all scalars and test functions (GAP A, §2), but for each fixed scalar `c` and test function `φ`,
`hC ω (c φ) = c hC ω φ` almost surely. The proof is the zero-variance principle `ae_eq_integral_of_variance_eq_zero`
(as in `ae_circleAverage_one_zero`), applied to `Y - c X` with `X = hC(φ)`, `Y = hC(cφ)`; the covariance is the kernel
`wholePlaneGFFCov` of `covariance_eq`. No new input.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory

/-- The pairing observable of `c φ` smears like `c` times the pairing observable of `φ`. -/
theorem smear_pairing_const_mul_test (c : ℝ) (φ f : ℂ → ℝ) :
    (GFFObservable.pairing (fun z => c * φ z)).smear f = c * (GFFObservable.pairing φ).smear f := by
  simp only [GFFObservable.smear]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- The pairing observable smears a scalar multiple of the integrand: `∫ φ (c f) = c ∫ φ f`. -/
theorem smear_pairing_const_mul_fun (c : ℝ) (φ f : ℂ → ℝ) :
    (GFFObservable.pairing φ).smear (fun x => c * f x) = c * (GFFObservable.pairing φ).smear f := by
  simp only [GFFObservable.smear]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- Covariance of pairings is linear in the first test function. -/
theorem wholePlaneGFFCov_pairing_const_mul_left (c : ℝ) (φ ψ : ℂ → ℝ) :
    wholePlaneGFFCov (GFFObservable.pairing (fun z => c * φ z)) (GFFObservable.pairing ψ)
      = c * wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing ψ) := by
  unfold wholePlaneGFFCov
  exact smear_pairing_const_mul_test c φ _

/-- Covariance of pairings is linear in the second test function. -/
theorem wholePlaneGFFCov_pairing_const_mul_right (c : ℝ) (φ ψ : ℂ → ℝ) :
    wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing (fun z => c * ψ z))
      = c * wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing ψ) := by
  unfold wholePlaneGFFCov
  have h : ∀ x : ℂ, (GFFObservable.pairing (fun z => c * ψ z)).smear (fun y => wholePlaneCov x y)
      = c * (GFFObservable.pairing ψ).smear (fun y => wholePlaneCov x y) :=
    fun x => smear_pairing_const_mul_test c ψ _
  simp only [h]
  exact smear_pairing_const_mul_fun c φ _

namespace IsWholePlaneGFF

/-- A pairing with an admissible test function is Gaussian (the single observable of `isGaussianProcess`). -/
theorem hasGaussianLaw_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    HasGaussianLaw (fun ω => hC ω φ) P :=
  hh.isGaussianProcess.hasGaussianLaw_eval (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)

/-- **A.s. homogeneity for a fixed scalar and test function** (operator note 01:44 UTC, option (b)):
`hC ω (c φ) = c · hC ω φ` for almost every `ω`. The statement is for each fixed `c` and `φ`; the simultaneous version over
all `c` and `φ` is not a consequence of `IsWholePlaneGFF` (GAP A). -/
theorem ae_pairing_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (c : ℝ) (φ : ℂ → ℝ)
    (hφ : IsTestFunction Set.univ φ) :
    (fun ω => hC ω (fun z => c * φ z)) =ᵐ[P] (fun ω => c * hC ω φ) := by
  have := hG.isProbabilityMeasure
  have hφc : IsTestFunction Set.univ (fun z => c * φ z) :=
    ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left, Set.subset_univ _⟩
  have hX : MemLp (fun ω => hC ω φ) 2 P := (hG.hasGaussianLaw_pairing hφ).memLp (by simp)
  have hY : MemLp (fun ω => hC ω (fun z => c * φ z)) 2 P :=
    (hG.hasGaussianLaw_pairing hφc).memLp (by simp)
  have hB : MemLp (fun ω => c * hC ω φ) 2 P := hX.const_mul c
  have hZ : MemLp (fun ω => hC ω (fun z => c * φ z) - c * hC ω φ) 2 P := hY.sub hB
  have hmeanX : ∫ ω, hC ω φ ∂P = 0 := hG.integral_eq_zero (.pairing φ) hφ
  have hmeanY : ∫ ω, hC ω (fun z => c * φ z) ∂P = 0 :=
    hG.integral_eq_zero (.pairing (fun z => c * φ z)) hφc
  -- covariances of the pair (Y, X), with V the covariance of X with itself
  have hXX : covariance (fun ω => hC ω φ) (fun ω => hC ω φ) P
      = wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing φ) :=
    hG.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  have hYX : covariance (fun ω => hC ω (fun z => c * φ z)) (fun ω => hC ω φ) P
      = c * wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing φ) := by
    rw [← wholePlaneGFFCov_pairing_const_mul_left]
    exact hG.covariance_eq (.pairing (fun z => c * φ z)) (.pairing φ) hφc hφ
  have hXY : covariance (fun ω => hC ω φ) (fun ω => hC ω (fun z => c * φ z)) P
      = c * wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing φ) := by
    rw [← wholePlaneGFFCov_pairing_const_mul_right]
    exact hG.covariance_eq (.pairing φ) (.pairing (fun z => c * φ z)) hφ hφc
  have hYY : covariance (fun ω => hC ω (fun z => c * φ z)) (fun ω => hC ω (fun z => c * φ z)) P
      = c * (c * wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing φ)) := by
    rw [← wholePlaneGFFCov_pairing_const_mul_left, ← wholePlaneGFFCov_pairing_const_mul_right]
    exact hG.covariance_eq (.pairing (fun z => c * φ z)) (.pairing (fun z => c * φ z)) hφc hφc
  -- the variance of Y - c X vanishes
  have hvar : Var[fun ω => hC ω (fun z => c * φ z) - c * hC ω φ; P] = 0 := by
    rw [← covariance_self hZ.aemeasurable]
    rw [covariance_fun_sub_left hY hB hZ, covariance_fun_sub_right hY hY hB,
      covariance_fun_sub_right hB hY hB, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_left, covariance_const_mul_right]
    rw [hYY, hYX, hXY, hXX]
    ring
  have hint : ∫ ω, (hC ω (fun z => c * φ z) - c * hC ω φ) ∂P = 0 := by
    rw [integral_sub (hY.integrable (by norm_num)) (hB.integrable (by norm_num)), integral_const_mul,
      hmeanX, hmeanY]
    ring
  filter_upwards [ae_eq_integral_of_variance_eq_zero hZ hvar] with ω hω
  have h2 : hC ω (fun z => c * φ z) - c * hC ω φ = 0 := hω.trans hint
  linarith

end IsWholePlaneGFF

end HarmonicBalls
