import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Step 8 helper: characteristic functions of finite Gaussian families

Source: corrected paper, lemma `s11-pinch:lem:mixing` (tex lines 3769-3812), via Gaussian cylinder approximation.
Probability facts from Mathlib only (no GFF input): a real linear combination `∑ θ_k Z_k` of a jointly Gaussian
centred family has characteristic function `exp(-Var/2)` with `Var = ∑ θ_k θ_l cov[Z_k, Z_l]`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ProbabilityTheory

namespace HarmonicBalls

/-- A real linear combination of a jointly Gaussian finite family is Gaussian. -/
theorem hasGaussianLaw_linComb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
    {Z : ι → Ω → ℝ} (hZ : HasGaussianLaw (fun ω (k : ι) => Z k ω) P) (θ : ι → ℝ) :
    HasGaussianLaw (fun ω => ∑ k, θ k * Z k ω) P := by
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ k, θ k • (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ)
  have h := hZ.map L
  convert h using 1
  funext ω
  simp [L]

/-- Each coordinate of a jointly Gaussian family is Gaussian, hence square integrable. -/
theorem memLp_two_of_hasGaussianLaw_fam {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
    {Z : ι → Ω → ℝ} (hZ : HasGaussianLaw (fun ω (k : ι) => Z k ω) P) (k : ι) :
    MemLp (Z k) 2 P := by
  have h := hZ.map (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ)
  exact ((h : HasGaussianLaw (Z k) P)).memLp_two

/-- Covariance of two weighted sums: `cov[∑ θ_k X_k, ∑ η_l Y_l] = ∑_k ∑_l θ_k η_l cov[X_k, Y_l]`. -/
theorem covariance_linComb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {X Y : ι → Ω → ℝ} (hX : ∀ k, MemLp (X k) 2 P) (hY : ∀ l, MemLp (Y l) 2 P)
    (θ η : ι → ℝ) :
    cov[fun ω => ∑ k, θ k * X k ω, fun ω => ∑ l, η l * Y l ω; P]
      = ∑ k, ∑ l, θ k * η l * cov[X k, Y l; P] := by
  have e1 : (fun ω => ∑ k, θ k * X k ω) = ∑ k, θ k • X k := by
    funext ω; simp [Finset.sum_apply, smul_eq_mul]
  have e2 : (fun ω => ∑ l, η l * Y l ω) = ∑ l, η l • Y l := by
    funext ω; simp [Finset.sum_apply, smul_eq_mul]
  rw [e1, e2, covariance_sum_left (fun k => (hX k).const_smul (θ k))
    (memLp_finsetSum' _ (fun l _ => (hY l).const_smul (η l)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [covariance_comm, covariance_sum_left (fun l => (hY l).const_smul (η l))
    ((hX k).const_smul (θ k))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [covariance_smul_left, covariance_smul_right, covariance_comm]
  ring

/-- The characteristic function of a centred jointly Gaussian linear combination:
`E exp(i ∑ θ_k Z_k) = exp(-(∑ θ_k θ_l cov[Z_k, Z_l]) / 2)`. -/
theorem integral_exp_linComb_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {Z : ι → Ω → ℝ} (hZ : HasGaussianLaw (fun ω (k : ι) => Z k ω) P)
    (hcent : ∀ k, P[Z k] = 0) (θ : ι → ℝ) :
    ∫ ω, Complex.exp (((∑ k, θ k * Z k ω : ℝ) : ℂ) * I) ∂P
      = Complex.exp (-((∑ k, ∑ l, θ k * θ l * cov[Z k, Z l; P] : ℝ) : ℂ) / 2) := by
  have hW := hasGaussianLaw_linComb hZ θ
  have hZm : ∀ k, MemLp (Z k) 2 P := memLp_two_of_hasGaussianLaw_fam hZ
  have hWm : MemLp (fun ω => ∑ k, θ k * Z k ω) 2 P := hW.memLp_two
  have hmean : P[fun ω => ∑ k, θ k * Z k ω] = 0 := by
    rw [integral_finsetSum]
    · simp [integral_const_mul, hcent]
    · intro k _
      exact ((hZm k).integrable one_le_two).const_mul (θ k)
  have hvar : Var[fun ω => ∑ k, θ k * Z k ω; P] = ∑ k, ∑ l, θ k * θ l * cov[Z k, Z l; P] := by
    rw [← covariance_self hWm.aemeasurable, covariance_linComb hZm hZm θ θ]
  have hmap := hW.map_eq_gaussianReal
  rw [hmean] at hmap
  have hmeas : AEMeasurable (fun ω => ∑ k, θ k * Z k ω) P := hWm.aemeasurable
  have hvarnn : Var[fun ω => ∑ k, θ k * Z k ω; P] ≥ 0 := variance_nonneg _ _
  calc ∫ ω, Complex.exp (((∑ k, θ k * Z k ω : ℝ) : ℂ) * I) ∂P
      = ∫ x, Complex.exp ((x : ℂ) * I) ∂(P.map (fun ω => ∑ k, θ k * Z k ω)) := by
        rw [integral_map hmeas (Continuous.aestronglyMeasurable (by fun_prop))]
    _ = charFun (P.map (fun ω => ∑ k, θ k * Z k ω)) 1 := by
        rw [charFun_apply_real]
        simp
    _ = charFun (gaussianReal 0 (Var[fun ω => ∑ k, θ k * Z k ω; P]).toNNReal) 1 := by
        rw [hmap]
    _ = Complex.exp (-((∑ k, ∑ l, θ k * θ l * cov[Z k, Z l; P] : ℝ) : ℂ) / 2) := by
        rw [charFun_gaussianReal, ← hvar]
        congr 1
        simp [Real.coe_toNNReal _ hvarnn]
        ring

end HarmonicBalls
