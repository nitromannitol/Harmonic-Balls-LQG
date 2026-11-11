import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Smooth log-shift cut off near the origin (write-up Step 11, the function `u_z`)

For `z ≠ 0` and a radius `b` with `2b < min(|z|, 1)`, there is a smooth compactly supported `u` with zero unit-circle
average that agrees with `-α₀ log|· + z|` on the ball `B_b(0)`. This is the write-up's `u_z ∈ C_c^∞(B_{2b}(z))` equal to
`-α₀ log|·|` on `B_b(z)`, translated to the origin: the rooted insertion at `z` is `-α₀ log|·+z|` near `0`
(the translation `y ↦ z + y`). Its unit-circle average is zero because the support lies in `B_{2b}(0) ⊂ B_1(0)`.
The cut-off is `Real.smoothTransition ((2b - ‖y‖)/b)`, equal to `1` on `B_b(0)` and to `0` outside `B_{2b}(0)`.
Source: Step 11 of the written proof (choice of `u_z`).
-/

open Metric Filter Topology
open scoped ContDiff

namespace HarmonicBalls

theorem exists_log_shift_cutoff (α₀ : ℝ) (z : ℂ) (b : ℝ) (hb : 0 < b) (hbz : 2 * b < ‖z‖) (hb1 : 2 * b < 1) :
    ∃ u : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧
      ∀ y ∈ ball (0 : ℂ) b, u y = -α₀ * Real.log ‖y + z‖ := by
  let c : ℂ → ℝ := fun y => Real.smoothTransition ((2 * b - ‖y‖) / b)
  -- the cut-off is zero where `‖y‖ > 2b`
  have hc0 : ∀ y : ℂ, 2 * b < ‖y‖ → c y = 0 := by
    intro y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_iff.2 (Or.inr ⟨by linarith, hb.le⟩)
  -- the cut-off is one where `‖y‖ < b`
  have hc1 : ∀ y : ℂ, ‖y‖ < b → c y = 1 := by
    intro y hy
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hb]
    linarith
  -- smoothness of the cut-off
  have hcont : ∀ y0 : ℂ, ContDiffAt ℝ (⊤ : ℕ∞) c y0 := by
    intro y0
    by_cases h0 : ‖y0‖ < b
    · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h0] with y hy
      exact hc1 y hy
    · have hy0 : y0 ≠ 0 := by
        rintro rfl
        simp at h0
        linarith
      exact (Real.smoothTransition.contDiff.contDiffAt).comp y0
        ((contDiffAt_const.sub (contDiffAt_norm ℝ hy0)).div_const b)
  refine ⟨fun y => c y * (-α₀ * Real.log ‖y + z‖), ?_, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun y0 => ?_
    by_cases hy : y0 + z = 0
    · -- near `-z` the cut-off vanishes, since `‖-z‖ = ‖z‖ > 2b`
      have hyz : 2 * b < ‖y0‖ := by
        have h' : y0 = -z := eq_neg_of_add_eq_zero_left hy
        rw [h', norm_neg]
        exact hbz
      have hev : (fun y : ℂ => c y * (-α₀ * Real.log ‖y + z‖)) =ᶠ[𝓝 y0] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hyz] with y hy'
        simp [hc0 y hy']
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hne : ‖y0 + z‖ ≠ 0 := norm_ne_zero_iff.2 hy
      have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => -α₀ * Real.log ‖y + z‖) y0 :=
        contDiffAt_const.mul (((contDiffAt_id.add contDiffAt_const).norm ℝ hy).log hne)
      exact (hcont y0).mul hg
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * b)) fun y hy => ?_
    have hy' : 2 * b < ‖y‖ := by
      simp only [mem_closedBall, dist_zero_right, not_le] at hy
      exact hy
    simp [hc0 y hy']
  · have hzero : Real.circleAverage (fun y : ℂ => c y * (-α₀ * Real.log ‖y + z‖)) 0 1 =
        Real.circleAverage (fun _ : ℂ => (0 : ℝ)) 0 1 := by
      refine Real.circleAverage_congr_sphere fun y hy => ?_
      have hy1 : ‖y‖ = 1 := by simpa using hy
      simp [hc0 y (by linarith)]
    rw [hzero]
    exact Real.circleAverage_const (0 : ℝ) 0 1
  · intro y hy
    have hy' : ‖y‖ < b := by simpa [dist_zero_right] using hy
    simp [hc1 y hy']

end HarmonicBalls
