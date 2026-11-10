import HarmonicBalls.FirstPass.S11i.MixingCanonical
import HarmonicBalls.FirstPass.S11i.DilationMixing

/-!
# The inverse of the dual dilation `dilOp` (fp-S11s-11-13-B1-covariance, step B3)

`dilOp L i = L (dilateTest 1 i)` with `dilateTest 1 k y = 4 k(2 y)` (S11i/DilationMixing.lean). Its inverse on mean-zero
test functions is `dilateTestInv k y = (1/4) k(y/2)`; hence `dilOp` is a bijection of the canonical space, with
measurable inverse `dilOpInv` (used for the two-sided invariance of the covariance event, ruling section 3 part C).
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- The inverse of `dilateTest 1` on functions: `(κ⁻¹ k)(y) = (1/4) k(y/2)`. -/
noncomputable def dilateTestInv (k : ℂ → ℝ) (y : ℂ) : ℝ :=
  (1 / 4 : ℝ) * k ((1 / 2 : ℝ) • y)

theorem isTestFunction_dilateTestInv {k : ℂ → ℝ} (hk : IsTestFunction univ k) :
    IsTestFunction univ (dilateTestInv k) := by
  obtain ⟨h1, h2, -⟩ := hk
  refine ⟨contDiff_const.mul (h1.comp (contDiff_id.const_smul (1 / 2 : ℝ))), ?_, subset_univ _⟩
  have hc : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have h3 : HasCompactSupport (fun y : ℂ => k ((1 / 2 : ℝ) • y)) :=
    h2.comp_homeomorph (Homeomorph.smulOfNeZero (1 / 2 : ℝ) hc)
  exact h3.mul_left

/-- Change of variables for the mean: `∫ (κ⁻¹ k) = ∫ k`, the inverse of `integral_dilateTest` at `n = 1`. -/
theorem integral_dilateTestInv (k : ℂ → ℝ) : ∫ y, dilateTestInv k y = ∫ z, k z := by
  unfold dilateTestInv
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure ℂ) k (1 / 2 : ℝ), Complex.finrank_real_complex]
  rw [smul_eq_mul]
  ring

/-- The inverse dual dilation on the canonical space: `(dilOpInv L) i = L (dilateTestInv i)`. -/
noncomputable def dilOpInv : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ) :=
  fun L i => L ⟨dilateTestInv i.1, isTestFunction_dilateTestInv i.2.1, (integral_dilateTestInv i.1).trans i.2.2⟩

theorem dilOp_dilOpInv (L : ModConstTestPairings (univ : Set ℂ)) : dilOp (dilOpInv L) = L := by
  funext i
  simp only [dilOp, dilOpInv]
  congr 1
  apply Subtype.ext
  funext y
  have h : (2 : ℝ) ^ 1 • ((1 / 2 : ℝ) • y) = y := by
    rw [smul_smul]
    norm_num
  simp only [dilateTestInv, dilateTest, h]
  ring

theorem dilOpInv_dilOp (L : ModConstTestPairings (univ : Set ℂ)) : dilOpInv (dilOp L) = L := by
  funext i
  simp only [dilOp, dilOpInv]
  congr 1
  apply Subtype.ext
  funext y
  have h : (1 / 2 : ℝ) • ((2 : ℝ) ^ 1 • y) = y := by
    rw [smul_smul]
    norm_num
  simp only [dilateTestInv, dilateTest, h]
  ring

theorem measurable_dilOpInv : Measurable (dilOpInv : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- The dual dilation as a measurable equivalence of the canonical space, with inverse `dilOpInv`. -/
noncomputable def dilOpEquiv : ModConstTestPairings (univ : Set ℂ) ≃ᵐ ModConstTestPairings (univ : Set ℂ) where
  toFun := dilOp
  invFun := dilOpInv
  left_inv := dilOpInv_dilOp
  right_inv := dilOp_dilOpInv
  measurable_toFun := measurable_dilOp
  measurable_invFun := measurable_dilOpInv

end HarmonicBalls
