import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Step 2 of the rooted decoder identification: the smooth shift `u_z`

Step 2, equations (3)-(4).
For a root `z` and radii with `2 b < ‖z‖` and `2 b < 1`, the function
`u_z(w) = -α₀ χ(w) log ‖z + w‖`, with `χ` a smooth bump equal to `1` on `ball 0 b`
and supported in `closedBall 0 (2 b)`, is smooth, compactly supported, has unit circle average zero,
and equals `-α₀ log ‖z + ·‖` on `ball 0 b`. These are the clauses of `hId` (smoothness, compact
support, circle average zero) plus the local shift identity used in Step 3.
-/

open Metric Set Filter Topology
open scoped ContDiff

namespace FirstPassS11ai

/-- The shift `u_z(w) = -α₀ χ(w) log ‖z + w‖` of Step 2,
with `χ` a smooth bump equal to `1` on `closedBall 0 b` and supported in `closedBall 0 (2 b)`. -/
theorem exists_shift_cutoff (z : ℂ) (α₀ : ℝ) {b : ℝ} (hb : 0 < b) (hbz : 2 * b < ‖z‖) (hb1 : 2 * b < 1) :
    ∃ u : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧
      ∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖ := by
  let B : ContDiffBump (0 : ℂ) := ⟨b, 2 * b, hb, by linarith⟩
  have hB1 : ∀ w ∈ ball (0 : ℂ) b, B w = 1 := by
    intro w hw
    apply B.one_of_mem_closedBall
    show w ∈ closedBall (0 : ℂ) b
    exact mem_closedBall.2 (mem_ball.1 hw).le
  have hB0 : ∀ w : ℂ, 2 * b ≤ dist w 0 → B w = 0 := fun w hw => B.zero_of_le_dist hw
  have hBsm : ContDiff ℝ (⊤ : ℕ∞) B := B.contDiff
  refine ⟨fun w => -α₀ * B w * Real.log ‖z + w‖, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w0
    by_cases h0 : z + w0 = 0
    · have hw0 : w0 ∉ closedBall (0 : ℂ) (2 * b) := by
        intro h
        rw [mem_closedBall_zero_iff] at h
        have hwz : w0 = -z := by linear_combination h0
        rw [hwz, norm_neg] at h
        linarith
      have hev : ∀ᶠ w in 𝓝 w0, 2 * b ≤ dist w 0 := by
        have hopen : IsOpen {w : ℂ | 2 * b < dist w 0} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        have hw0' : 2 * b < dist w0 0 := not_le.1 (fun h => hw0 (mem_closedBall.2 h))
        filter_upwards [hopen.mem_nhds hw0'] with w hw using hw.le
      have hu0 : (fun w => -α₀ * B w * Real.log ‖z + w‖) =ᶠ[𝓝 w0] 0 := by
        filter_upwards [hev] with w hw
        simp [hB0 w hw]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hu0
    · have hn : ‖z + w0‖ ≠ 0 := norm_ne_zero_iff.2 h0
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ‖y‖) (z + w0) :=
        contDiffAt_norm ℝ h0
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => Real.log ‖y‖) (z + w0) :=
        (Real.contDiffAt_log.2 hn).comp (z + w0) h1
      have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => Real.log ‖z + w‖) w0 :=
        h2.comp w0 (contDiff_const.add contDiff_id).contDiffAt
      exact (contDiffAt_const.mul hBsm.contDiffAt).mul h3
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * b))
    intro w hw
    have hd : 2 * b ≤ dist w 0 := (not_le.1 (fun h => hw (mem_closedBall.2 h))).le
    simp [hB0 w hd]
  · have hcongr : Set.EqOn (fun w : ℂ => -α₀ * B w * Real.log ‖z + w‖)
        (fun _ => (0 : ℝ)) (sphere (0 : ℂ) |1|) := by
      intro w hw
      have hd : dist w 0 = 1 := by simpa using hw
      have hd' : 2 * b ≤ dist w 0 := by rw [hd]; exact hb1.le
      simp [hB0 w hd']
    rw [Real.circleAverage_congr_sphere hcongr, Real.circleAverage_const]
  · intro w hw
    simp [hB1 w hw]

end FirstPassS11ai
