import HarmonicBalls.Defs.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
A smooth perturbation on a neighborhood of a closed ball admits a compactly supported
representative with the same pairings against tests supported in that ball.
-/

open MeasureTheory Metric Set Filter
open scoped ContDiff Topology

namespace HarmonicBalls

/-- A locally smooth function on a ball has a test-function representative on every
smaller closed ball. -/
theorem exists_testFunction_eqOn_closedBall_of_contDiffOn_ball
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {g : ℂ → ℝ} (hg : ContDiffOn ℝ ∞ g (ball c R)) :
    ∃ f : ℂ → ℝ, IsTestFunction (ball c R) f ∧ EqOn f g (closedBall c r) := by
  let b : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hbR : b.rOut < R := by dsimp [b]; linarith
  refine ⟨fun x => b x * g x, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball c R
    · exact b.contDiff.contDiffAt.mul (hg.contDiffAt (isOpen_ball.mem_nhds hx))
    · have hxc : x ∈ (closedBall c b.rOut)ᶜ := by
        simp only [mem_compl_iff, mem_closedBall, not_le]
        have : R ≤ dist x c := by simpa [mem_ball, not_lt] using hx
        linarith
      have hn : (closedBall c b.rOut)ᶜ ∈ 𝓝 x :=
        isClosed_closedBall.isOpen_compl.mem_nhds hxc
      have heq : (fun y => b y * g y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hn] with y hy
        have hy' : b.rOut ≤ dist y c := by
          have : ¬ dist y c ≤ b.rOut := hy
          exact le_of_lt (lt_of_not_ge this)
        simp [b.zero_of_le_dist hy']
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact b.hasCompactSupport.mul_right
  · calc
      tsupport (fun x => b x * g x) ⊆ tsupport b := tsupport_mul_subset_left
      _ = closedBall c b.rOut := b.tsupport_eq
      _ ⊆ ball c R := closedBall_subset_ball hbR
  · intro x hx
    simp [b.one_of_mem_closedBall hx]

/-- Replacing a locally smooth shift by a function agreeing on the support of a
test leaves their integral pairing unchanged. -/
theorem integral_mul_eq_of_eqOn_tsupport {f g φ : ℂ → ℝ}
    (heq : EqOn f g (tsupport φ)) :
    (∫ x, φ x * f x) = ∫ x, φ x * g x := by
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [heq hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- A logarithmic insertion is smooth on any open set avoiding its singularity. -/
theorem contDiffOn_log_norm_add {z : ℂ} {U : Set ℂ}
    (hU : ∀ x ∈ U, z + x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x : ℂ => Real.log ‖z + x‖) U := by
  intro x hx
  have hzx : z + x ≠ 0 := hU x hx
  have h : ContDiffAt ℝ ∞ (fun x : ℂ => z + x) x :=
    contDiffAt_const.add contDiffAt_id
  exact ((h.norm ℝ hzx).log (norm_ne_zero_iff.mpr hzx)).contDiffWithinAt

/-- Away from its singularity, a logarithmic shift has a compactly supported smooth
representative agreeing on a smaller closed ball. -/
theorem exists_testFunction_eqOn_log_norm_add {c z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hU : ∀ x ∈ ball c R, z + x ≠ 0) :
    ∃ f : ℂ → ℝ, IsTestFunction (ball c R) f ∧
      EqOn f (fun x => Real.log ‖z + x‖) (closedBall c r) :=
  exists_testFunction_eqOn_closedBall_of_contDiffOn_ball hr hrR
    (contDiffOn_log_norm_add hU)

/-- One cutoff represents the logarithmic insertion simultaneously in every test
pairing supported on the smaller ball. -/
theorem exists_testFunction_log_norm_add_pairings {c z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hU : ∀ x ∈ ball c R, z + x ≠ 0) :
    ∃ f : ℂ → ℝ, IsTestFunction (ball c R) f ∧
      ∀ φ : ℂ → ℝ, tsupport φ ⊆ closedBall c r →
        (∫ x, φ x * f x) = ∫ x, φ x * Real.log ‖z + x‖ := by
  obtain ⟨f, hf, heq⟩ := exists_testFunction_eqOn_log_norm_add hr hrR hU
  exact ⟨f, hf, fun _ hφ => integral_mul_eq_of_eqOn_tsupport (heq.mono hφ)⟩

end HarmonicBalls
