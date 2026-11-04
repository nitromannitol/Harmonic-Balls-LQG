import HarmonicBalls.Proofs.Sec6.ContinuousHarmonic

/-! # A local planar Harnack inequality

The Poisson kernel gives a scale-independent bound on a concentric half-disc.
-/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace Real

/-- A nonnegative harmonic function on a closed disc is bounded on its
concentric half-disc by four times its value at the centre. -/
theorem harmonic_le_four_mul_center {f : ℂ → ℝ} {c x : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : HarmonicOnNhd f (closedBall c r))
    (hnonneg : ∀ z ∈ sphere c r, 0 ≤ f z) (hx : x ∈ closedBall c (r / 2)) :
    f x ≤ 4 * f c := by
  have hxr : x ∈ ball c r := by
    have hx' : dist x c ≤ r / 2 := hx
    show dist x c < r
    linarith
  have hci : CircleIntegrable f c r :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hkernel : ∀ ζ ∈ sphere c r, poissonKernel c x ζ ≤ 4 := by
    intro ζ hζ
    have hdist : r / 2 ≤ ‖ζ - x‖ := by
      have ht := dist_triangle ζ x c
      have hz : dist ζ c = r := hζ
      have hx' : dist x c ≤ r / 2 := hx
      have hd : r / 2 ≤ dist ζ x := by linarith
      simpa only [dist_eq_norm] using hd
    calc poissonKernel c x ζ
      _ ≤ (r ^ 2 - ‖x - c‖ ^ 2) / (r / 2) ^ 2 :=
        poissonKernel_le_of_le_norm (by positivity) hxr hζ hdist
      _ ≤ 4 := by
        apply (div_le_iff₀ (by positivity : 0 < (r / 2) ^ 2)).2
        nlinarith [sq_nonneg ‖x - c‖]
  have hbound : Real.circleAverage (poissonKernel c x • f) c r ≤
      Real.circleAverage (fun z => 4 * f z) c r := by
    apply circleAverage_mono (HarmonicBalls.CircleIntegrable.poissonKernel_smul hci hxr)
      ((continuousOn_const.mul (hf.continuousOn.mono sphere_subset_closedBall)).circleIntegrable hr.le)
    intro ζ hζ
    rw [abs_of_pos hr] at hζ
    change poissonKernel c x ζ * f ζ ≤ 4 * f ζ
    exact mul_le_mul_of_nonneg_right (hkernel ζ hζ) (hnonneg ζ hζ)
  have hrepr := hf.circleAverage_poissonKernel_smul hxr
  have hmean : Real.circleAverage f c r = f c :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa only [abs_of_pos hr] using hf)
  rw [hrepr] at hbound
  have havg : Real.circleAverage (fun z => 4 * f z) c r = 4 * f c := by
    rw [show (fun z => 4 * f z) = (4 : ℝ) • f by ext z; simp]
    rw [circleAverage_smul, hmean, smul_eq_mul]
  rwa [havg] at hbound

end HarmonicBalls.Section6
