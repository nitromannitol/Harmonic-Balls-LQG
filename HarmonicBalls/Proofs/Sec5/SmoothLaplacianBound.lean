import HarmonicBalls.Defs.Laplacian
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Smooth functions and the distributional Laplacian

Integration by parts transfers pointwise bounds on the Laplacian of a smooth
compactly supported function to the distributional inequality used for
supersolutions.
-/

namespace HarmonicBalls

open MeasureTheory Laplacian
open scoped ContDiff

/-- Integration by parts for two smooth compactly supported functions. -/
theorem integral_mul_laplacian_eq_laplacian_mul_of_compactSupport
    {f g : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, f x * Δ g x = ∫ x, Δ f x * g x := by
  have h := SchwartzMap.integral_mul_laplacian_right_eq_left
      (μ := volume) (hfc.toSchwartzMap hf) (hgc.toSchwartzMap hg)
  simp only [SchwartzMap.laplacian_apply] at h
  change (∫ x, f x * Δ g x) = ∫ x, Δ f x * g x at h
  exact h

/-- A pointwise upper bound on a smooth compactly supported function's
Laplacian gives the corresponding distributional bound by Lebesgue measure. -/
theorem laplacianLE_of_smooth_compactSupport_of_bound
    {f : ℂ → ℝ} {C : ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hC : 0 ≤ C) (hbound : ∀ x, Δ f x ≤ C) (U : Set ℂ) :
    LaplacianLE f (ENNReal.ofReal C • volume) U := by
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn U, ?_⟩
  intro φ hφ hφ0 hφμ
  rw [integral_mul_laplacian_eq_laplacian_mul_of_compactSupport hf hfc hφ.1 hφ.2.1]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hC, smul_eq_mul, ← integral_const_mul]
  apply integral_mono
  · have hi := (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
        (Δ (hfc.toSchwartzMap hf)) (hφ.2.1.toSchwartzMap hφ.1)).integrable (μ := volume)
    change Integrable (fun x => (Δ (hfc.toSchwartzMap hf)) x * φ x) volume at hi
    simp only [SchwartzMap.laplacian_apply] at hi
    change Integrable (fun x => Δ f x * φ x) at hi
    exact hi
  · exact (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).const_mul C
  · intro x
    exact mul_le_mul_of_nonneg_right (hbound x) (hφ0 x)

/-- Every smooth compactly supported function is bounded above in the
weak Laplacian sense by a constant multiple of area measure. -/
theorem exists_laplacianLE_smooth_compactSupport
    {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set ℂ, LaplacianLE f (ENNReal.ofReal C • volume) U := by
  let F := Δ (hfc.toSchwartzMap hf)
  let C := max 1 (SchwartzMap.seminorm ℝ 0 0 F)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbound : ∀ x, Δ f x ≤ C := by
    intro x
    have h := SchwartzMap.norm_le_seminorm ℝ F x
    change ‖(Δ (hfc.toSchwartzMap hf)) x‖ ≤ _ at h
    rw [SchwartzMap.laplacian_apply] at h
    change ‖Δ f x‖ ≤ _ at h
    exact (le_trans (le_abs_self _) (le_trans (by simpa only [Real.norm_eq_abs] using h)
      (le_max_right _ _)))
  exact ⟨C, hC, laplacianLE_of_smooth_compactSupport_of_bound hf hfc hC.le hbound⟩

end HarmonicBalls
