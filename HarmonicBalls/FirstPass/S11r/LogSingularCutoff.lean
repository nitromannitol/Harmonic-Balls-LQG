import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Smooth cut-off of a logarithmic singularity at a point (fp-S11r, owner n2)

Pure analysis for step (d) of the plan for (20) (CHATGPT-n3-B1-B2.md section 4.2): on a disk `V` avoiding the root `z`,
the rooted field `f_z = h^ℂ - α log|·| - γ log|· - z| + γ log max(1,|·|)` equals `h^ℂ + f` for a smooth compactly
supported `f` with zero unit-circle average (the Cameron-Martin shift of `ae_mem_addFunPairing_of_ae_mem`,
CMShift.lean). The singularity is `-β log|· - p|`; the cut-off is `χ · (-β log|· - p|)` with `χ` a `ContDiffBump`
centred at `c`, equal to one on `closedBall c r`, supported in `ball c R` with `closedBall c R ⊆ B₁ ∖ {p}`.

* `circleAverage_unit_zero_of_vanish`: a function vanishing on the unit circle has zero unit-circle average.
* `exists_log_sing_cutoff`: the cut-off itself, with support in `ball c R` (so zero on the unit circle).
-/

namespace HarmonicBalls

open Metric Complex

/-- A function vanishing on the unit circle has zero unit-circle average (Armitage-Gardiner: the circle mean of a
function supported away from the circle is zero). -/
theorem circleAverage_unit_zero_of_vanish {f : ℂ → ℝ} (h : ∀ x : ℂ, ‖x‖ = 1 → f x = 0) :
    Real.circleAverage f 0 1 = 0 := by
  unfold Real.circleAverage
  simp [h, norm_circleMap_zero]

/-- Smooth cut-off of the logarithmic singularity `-β log|· - p|` at `p` on a disk `ball c r`: for `0 < r < R` with
`R < dist p c` and `closedBall c R ⊆ B₁`, there is a smooth compactly supported `f` with zero unit-circle average, which
vanishes outside `ball c R` and equals `-β log|· - p|` on `ball c r`. -/
theorem exists_log_sing_cutoff (β : ℝ) {c p : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hpR : R < dist p c)
    (hU : closedBall c R ⊆ ball (0 : ℂ) 1) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ Real.circleAverage f 0 1 = 0 ∧
      (∀ x : ℂ, R ≤ dist x c → f x = 0) ∧ ∀ x ∈ ball c r, f x = -β * Real.log ‖x - p‖ := by
  let B : ContDiffBump c :=
    { rIn := r, rOut := (r + R) / 2, rIn_pos := hr, rIn_lt_rOut := by linarith }
  have hBz : ∀ y : ℂ, (r + R) / 2 ≤ dist y c → B y = 0 := fun y hy => B.zero_of_le_dist hy
  -- on the unit circle, `dist x c > R`
  have hout : ∀ x : ℂ, ‖x‖ = 1 → R < dist x c := by
    intro x hx
    by_contra hcon
    have hle : dist x c ≤ R := not_lt.1 hcon
    have hmem : x ∈ ball (0 : ℂ) 1 := hU (mem_closedBall.2 hle)
    rw [mem_ball, dist_zero_right, hx] at hmem
    exact lt_irrefl _ hmem
  refine ⟨fun x => B x * (-β * Real.log ‖x - p‖), ?_, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = p
    · -- near the singularity the bump vanishes
      have hd : (r + R) / 2 < dist x c := by rw [hx]; linarith
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x (sub_pos.2 hd)] with y hy
      have hy' : dist y x < dist x c - (r + R) / 2 := by simpa [mem_ball] using hy
      have hyc : (r + R) / 2 ≤ dist y c := by
        have := dist_triangle x y c
        rw [dist_comm x y] at this
        linarith
      simp [hBz y hyc]
    · have hne : x - p ≠ 0 := sub_ne_zero.2 hx
      have hL : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => -β * Real.log ‖y - p‖) x := by
        apply contDiffAt_const.mul
        exact (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hne)).comp x
          ((contDiffAt_norm ℝ hne).comp x (contDiffAt_id.sub contDiffAt_const))
      exact B.contDiff.contDiffAt.mul hL
  · exact B.hasCompactSupport.mul_right
  · apply circleAverage_unit_zero_of_vanish
    intro x hx
    simp [hBz x (by linarith [hout x hx])]
  · intro x hx
    simp [hBz x (by linarith)]
  · intro x hx
    have hB1 : B x = 1 := B.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hB1]

end HarmonicBalls
