import HarmonicBalls.Proofs.Sec7.TimeScaleBounds
import Mathlib.Analysis.Normed.Group.Pointwise

/-!
# Interpolation of the cluster continuity estimate

An estimate at all sufficiently small dyadic spatial scales implies the
continuous-time Hölder estimate.
-/

namespace HarmonicBalls

open Filter Metric Set Topology
open scoped Pointwise

/-- Interpolate dyadic confinement estimates to every sufficiently small
positive time increment. -/
theorem eventually_contained_of_dyadic_scales {A : Set ℂ} {B : ℝ → Set ℂ}
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (N : ℕ)
    (hscale : ∀ n ≥ N, ∀ T : ℝ, 0 < T → T ≤ α * (((2 : ℝ)⁻¹) ^ n) ^ (2 * β) →
      closure (B T) ⊆ A + ball 0 (70 * Real.sqrt (((2 : ℝ)⁻¹) ^ n))) :
    ∀ᶠ T in 𝓝[>] (0 : ℝ),
      closure (B T) ⊆ A + ball 0 ((140 * α ^ (-(4 * β)⁻¹)) * T ^ (1 / (4 * β))) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ N
  have hq : 0 < q := by dsimp [q]; positivity
  have hthreshold : 0 < α * q ^ (2 * β) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hthreshold] with T hT
  let x : ℝ := (T / α) ^ (2 * β)⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hT.1 hα) _
  have hxq : x < q := by
    have hdiv : T / α < q ^ (2 * β) := (div_lt_iff₀ hα).2 (by linarith [hT.2])
    calc
      x < (q ^ (2 * β)) ^ (2 * β)⁻¹ :=
        Real.rpow_lt_rpow (div_pos hT.1 hα).le hdiv (by positivity)
      _ = q := by rw [← Real.rpow_mul hq.le, mul_inv_cancel₀ (by positivity : 2 * β ≠ 0), Real.rpow_one]
  obtain ⟨n, hn, hxn, hnx⟩ := exists_late_dyadic_scale N hx hxq
  have htime := time_le_mul_rpow_of_scale hT.1 hα hβ hxn
  have hrad := sqrt_scale_le_time_rpow hT.1 hα hβ
    (show 0 ≤ ((2 : ℝ)⁻¹) ^ n by positivity) hnx.le
  have hsub := hscale n hn T hT.1 htime
  intro y hy
  obtain ⟨a, ha, b, hb, hab⟩ := hsub hy
  refine ⟨a, ha, b, ?_, hab⟩
  apply ball_subset_ball _ hb
  simpa only [one_div] using hrad

end HarmonicBalls
