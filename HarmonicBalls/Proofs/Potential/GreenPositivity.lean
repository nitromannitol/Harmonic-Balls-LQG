import HarmonicBalls.Defs.Green

/-!
# A lower bound for the Green function near its pole

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 2.2
(subsec:green, lines 466-489; Proposition 2.3, "Positive", line 483).

For a bounded open set `O ⊆ ℂ`, a closed disc `closedBall y r ⊆ O` (`r > 0`) and `0 < ‖x - y‖ < r`,
`(2π)⁻¹ log (r / ‖x - y‖) ≤ G_O(x,y)`; in particular `G_O(x,y) > 0` (`greenFunction_pos`).

The proof is the classical one (Armitage–Gardiner, *Classical Potential Theory*, §4.1): every harmonic minorant `h`
of the Newtonian kernel `N(x,·)` on `O` satisfies, by the mean value property on `closedBall y r`,
`h y = ⨍_{∂B_r(y)} h ≤ ⨍_{∂B_r(y)} N(x,·) = -(2π)⁻¹ log r`, the last identity being Jensen's formula for the
logarithm (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). Hence the greatest harmonic minorant is at
most `-(2π)⁻¹ log r` at `y`, and `G_O(x,y) = N(x,y) - I_O[N(x,·)](y) ≥ (2π)⁻¹ log (r / ‖x - y‖)`.

## Main statements

* `circleAverage_newtonKernel`: `⨍_{∂B_r(y)} N(x,·) = -(2π)⁻¹ log r` for `‖x - y‖ ≤ r`;
* `IsHarmonicMinorant.le_neg_mul_log_radius`: the bound `h y ≤ -(2π)⁻¹ log r` for harmonic minorants;
* `log_div_le_greenFunction`: `(2π)⁻¹ log (r / ‖x - y‖) ≤ G_O(x,y)`;
* `greenFunction_pos`: `0 < G_O(x,y)` under the same hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric InnerProductSpace

/-- The circle average of the Newtonian kernel with pole `x` over a circle `∂B_r(y)` enclosing the pole
(`‖x - y‖ ≤ r`) is `-(2π)⁻¹ log r` (Jensen's formula for `log ‖· - x‖`). -/
theorem circleAverage_newtonKernel {x y : ℂ} {r : ℝ} (hr : 0 < r) (hxy : ‖x - y‖ ≤ r) :
    Real.circleAverage (newtonKernel x) y r = -(2 * Real.pi)⁻¹ * Real.log r := by
  have hfun : newtonKernel x = fun w => (-(2 * Real.pi)⁻¹) • Real.log ‖w - x‖ := by
    funext w
    simp [newtonKernel, norm_sub_rev, smul_eq_mul]
  have hle : |r⁻¹ * ‖y - x‖| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr, mul_one, norm_sub_rev]
    exact hxy
  rw [hfun, Real.circleAverage_fun_smul, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne',
    (Real.posLog_eq_zero_iff _).2 hle, add_zero, smul_eq_mul]

/-- The Newtonian kernel with pole `x` is continuous on every circle `∂B_r(y)` not passing through `x`. -/
theorem continuousOn_newtonKernel_sphere {x y : ℂ} {r : ℝ} (hx : x ∉ sphere y r) :
    ContinuousOn (newtonKernel x) (sphere y r) := by
  refine continuousOn_const.mul (ContinuousOn.log (continuous_const.sub continuous_id).norm.continuousOn ?_)
  intro w hw
  rw [norm_ne_zero_iff, sub_ne_zero]
  rintro rfl
  exact hx hw

/-- *Harmonic minorants of the Newtonian kernel are bounded at the center of a disc around the pole.* If `h` is a
harmonic minorant of `N(x,·)` on `O` and `closedBall y r ⊆ O` with `‖x - y‖ < r`, then `h y ≤ -(2π)⁻¹ log r`
(mean value property of `h` on `closedBall y r` and `circleAverage_newtonKernel`). -/
theorem IsHarmonicMinorant.le_neg_mul_log_radius {O : Set ℂ} {x y : ℂ} {r : ℝ} {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant O (newtonKernelEReal x) h) (hr : 0 < r) (hO : closedBall y r ⊆ O)
    (hxy : ‖x - y‖ < r) : h y ≤ -(2 * Real.pi)⁻¹ * Real.log r := by
  have hharm : HarmonicOnNhd h (closedBall y |r|) := by
    rw [abs_of_pos hr]
    exact fun w hw => hh.1 w (hO hw)
  have hxs : x ∉ sphere y r := by
    intro hx
    rw [mem_sphere, dist_eq_norm] at hx
    exact hxy.ne hx
  rw [← hharm.circleAverage_eq, ← circleAverage_newtonKernel hr hxy.le]
  refine Real.circleAverage_mono ((hharm.continuousOn.mono sphere_subset_closedBall).circleIntegrable')
    (ContinuousOn.circleIntegrable' (by rw [abs_of_pos hr]; exact continuousOn_newtonKernel_sphere hxs)) ?_
  intro w hw
  rw [abs_of_pos hr] at hw
  have hwx : w ≠ x := by
    rintro rfl
    exact hxs hw
  have hle := hh.2 w (hO (sphere_subset_closedBall hw))
  simpa [newtonKernelEReal, hwx] using hle

/-- *Lower bound for the Green function near its pole.* For `O` bounded, `closedBall y r ⊆ O` with `r > 0` and
`0 < ‖x - y‖ < r`, `(2π)⁻¹ log (r / ‖x - y‖) ≤ G_O(x,y)` (cf. Proposition 2.3, "Positive", line 483). -/
theorem log_div_le_greenFunction {O : Set ℂ} (hO : Bornology.IsBounded O) {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hyO : closedBall y r ⊆ O) (hxy₀ : 0 < ‖x - y‖) (hxy : ‖x - y‖ < r) :
    (2 * Real.pi)⁻¹ * Real.log (r / ‖x - y‖) ≤ greenFunction O x y := by
  have hx : x ∈ O := hyO (by rw [mem_closedBall, dist_eq_norm]; exact hxy.le)
  have hy : y ∈ O := hyO (mem_closedBall_self hr.le)
  have hne : x ≠ y := fun h => by simp [h] at hxy₀
  rw [greenFunction, ite_eq_left ⟨hx, hy, hne⟩]
  have hI : greatestHarmonicMinorant O (newtonKernelEReal x) y ≤
      ((-(2 * Real.pi)⁻¹ * Real.log r : ℝ) : EReal) :=
    iSup₂_le fun h hh => EReal.coe_le_coe_iff.2 (hh.le_neg_mul_log_radius hr hyO hxy)
  obtain ⟨R, hR⟩ := hO.subset_closedBall x
  have hbot : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      ((isHarmonicMinorant_const_newtonKernelEReal hR).le_greatestHarmonicMinorant y)
  have hle := EReal.toReal_le_toReal hI hbot (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at hle
  rw [Real.log_div hr.ne' hxy₀.ne', newtonKernel, mul_sub]
  linarith

/-- *Strict positivity of the Green function near its pole.* For `O` bounded, `closedBall y r ⊆ O` with `r > 0` and
`0 < ‖x - y‖ < r`, `0 < G_O(x,y)` (cf. Proposition 2.3, "Positive", line 483). -/
theorem greenFunction_pos {O : Set ℂ} (hO : Bornology.IsBounded O) {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hyO : closedBall y r ⊆ O) (hxy₀ : 0 < ‖x - y‖) (hxy : ‖x - y‖ < r) :
    0 < greenFunction O x y := by
  refine lt_of_lt_of_le (mul_pos (by positivity) (Real.log_pos ?_)) (log_div_le_greenFunction hO hr hyO hxy₀ hxy)
  rwa [one_lt_div hxy₀]

end HarmonicBalls
