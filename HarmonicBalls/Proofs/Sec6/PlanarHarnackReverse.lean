import HarmonicBalls.Proofs.Sec6.PlanarHarnack

/-! # Reverse local planar Harnack inequality -/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace Real

/-- On a concentric half-disc, the value at the centre is at most four times
the value at any point of a nonnegative harmonic function. -/
theorem harmonic_center_le_four_mul {f : ℂ → ℝ} {c x : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : HarmonicOnNhd f (closedBall c r))
    (hnonneg : ∀ z ∈ sphere c r, 0 ≤ f z) (hx : x ∈ closedBall c (r / 2)) :
    f c ≤ 4 * f x := by
  have hxr : x ∈ ball c r := by
    have hx' : dist x c ≤ r / 2 := hx
    show dist x c < r
    linarith
  have hci : CircleIntegrable f c r :=
    (hf.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr.le
  have hkernel : ∀ ζ ∈ sphere c r, (1 / 4 : ℝ) ≤ poissonKernel c x ζ := by
    intro ζ hζ
    have hz : dist ζ c = r := hζ
    have hx' : dist x c ≤ r / 2 := hx
    have hd : r / 2 ≤ dist ζ x := by
      have ht := dist_triangle ζ x c
      linarith
    have hdu : dist ζ x ≤ 3 * r / 2 := by
      have ht := dist_triangle ζ c x
      rw [dist_comm c x] at ht
      linarith
    rw [poissonKernel_def]
    have hz' : ‖ζ - c‖ = r := by simpa [dist_eq_norm] using hz
    have hx'' : ‖x - c‖ ≤ r / 2 := by simpa [dist_eq_norm] using hx'
    have hd' : r / 2 ≤ ‖ζ - x‖ := by simpa [dist_eq_norm] using hd
    have hdu' : ‖ζ - x‖ ≤ 3 * r / 2 := by simpa [dist_eq_norm] using hdu
    have he : ζ - c - (x - c) = ζ - x := by ring
    rw [hz', he]
    have hdn : 0 < ‖ζ - x‖ := by linarith
    apply (le_div_iff₀ (by positivity : 0 < ‖ζ - x‖ ^ 2)).2
    nlinarith [sq_nonneg ‖x - c‖, sq_nonneg ‖ζ - x‖,
      sq_nonneg (r / 2 - ‖x - c‖), sq_nonneg (3 * r / 2 - ‖ζ - x‖),
      norm_nonneg (x - c), norm_nonneg (ζ - x)]
  have hbound : Real.circleAverage (fun z => (1 / 4 : ℝ) * f z) c r ≤
      Real.circleAverage (poissonKernel c x • f) c r := by
    apply circleAverage_mono
      ((continuousOn_const.mul (hf.continuousOn.mono sphere_subset_closedBall)).circleIntegrable hr.le)
      (HarmonicBalls.CircleIntegrable.poissonKernel_smul hci hxr)
    intro ζ hζ
    rw [abs_of_pos hr] at hζ
    change (1 / 4 : ℝ) * f ζ ≤ poissonKernel c x ζ * f ζ
    exact mul_le_mul_of_nonneg_right (hkernel ζ hζ) (hnonneg ζ hζ)
  have hrepr := hf.circleAverage_poissonKernel_smul hxr
  have hmean : Real.circleAverage f c r = f c :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa only [abs_of_pos hr] using hf)
  have havg : Real.circleAverage (fun z => (1 / 4 : ℝ) * f z) c r = (1 / 4 : ℝ) * f c := by
    rw [show (fun z => (1 / 4 : ℝ) * f z) = (1 / 4 : ℝ) • f by ext z; simp]
    rw [circleAverage_smul, hmean, smul_eq_mul]
  rw [havg, hrepr] at hbound
  linarith

end HarmonicBalls.Section6
