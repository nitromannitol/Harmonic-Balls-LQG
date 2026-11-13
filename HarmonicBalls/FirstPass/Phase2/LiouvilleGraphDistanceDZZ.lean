import HarmonicBalls.Defs.LQGGraphDistance
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDScale

/-!
# The Liouville graph distance at mass `δ²` and the Ding-Zeitouni-Zhang distance

The Liouville graph distance `liouvilleGraphDistance μ ε z w` (Ding-Gwynne, arXiv:1807.01072v3,
Definition 1.3) is the least number of Euclidean balls of `μ`-mass at most `ε` whose union
contains a path from `z` to `w`. The distance `D_δ(z, w)` of Ding-Zeitouni-Zhang
(arXiv:1807.00422, l. 121-124), formalized as `LQGMetric.lgdDZZ`, uses balls with rational centres
and `μ`-mass at most `δ²`; `LQGMetric.lgdDZZ_eq_lgdFree` shows that the rationality of the centres
does not matter. Hence the two distances agree at `ε = δ²`, and an exponent `χ` of `D_δ(z, w)` as
`δ → 0` is an exponent `χ / 2` of the Liouville graph distance as `ε → 0`, i.e. the graph
dimension `2 / χ`.

* `liouvilleGraphDistance_sq_eq_lgdFree`, `liouvilleGraphDistance_sq_eq_lgdDZZ`: the identification.
* `isLiouvilleGraphDimension_of_tendsto_lgdDZZ`: the exponent `χ > 0` of `D_δ(z, w)` gives
  `IsLiouvilleGraphDimension μ z w (2 / χ)`.
-/

open MeasureTheory Filter Topology

namespace HarmonicBalls

/-- The Liouville graph distance at mass `δ²` is the free-centre distance `LQGMetric.lgdFree`. -/
theorem liouvilleGraphDistance_sq_eq_lgdFree (μ : Measure ℂ) (δ : ℝ) (z w : ℂ) :
    liouvilleGraphDistance μ (δ ^ 2) z w = LQGMetric.lgdFree μ δ z w := by
  unfold liouvilleGraphDistance LQGMetric.lgdFree
  apply le_antisymm
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨x, ρ, P, hm, hcov⟩ := hN
    exact sInf_le ⟨N, rfl, fun i => (x i, ρ i), hm, P, hcov⟩
  · refine le_sInf ?_
    rintro _ ⟨N, rfl, balls, hm, P, hcov⟩
    exact iInf₂_le N ⟨fun i => (balls i).1, fun i => (balls i).2, P, hm, hcov⟩

/-- **The Liouville graph distance at mass `δ²` is the Ding-Zeitouni-Zhang distance `D_δ`.** -/
theorem liouvilleGraphDistance_sq_eq_lgdDZZ (μ : Measure ℂ) (δ : ℝ) (z w : ℂ) :
    liouvilleGraphDistance μ (δ ^ 2) z w = LQGMetric.lgdDZZ μ δ z w := by
  rw [liouvilleGraphDistance_sq_eq_lgdFree, LQGMetric.lgdDZZ_eq_lgdFree]

/-- **An exponent of the Ding-Zeitouni-Zhang distance gives the graph dimension.** If
`log D_δ(z, w) / log δ⁻¹ → χ > 0` as `δ → 0⁺`, then the Liouville graph distance of `μ` between
`z` and `w` has dimension `2 / χ`. -/
theorem isLiouvilleGraphDimension_of_tendsto_lgdDZZ {μ : Measure ℂ} {z w : ℂ} {χ : ℝ}
    (hχ : 0 < χ)
    (h : Tendsto (fun δ : ℝ => Real.log (LQGMetric.lgdDZZ μ δ z w).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ)) :
    IsLiouvilleGraphDimension μ z w (2 / χ) := by
  refine isLiouvilleGraphDimension_of_fullScale (div_pos two_pos hχ) ?_
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε using Real.sqrt_pos.2 hε
  have hlim := (h.comp hsqrt).div_const 2
  rw [one_div_div]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hd : liouvilleGraphDistance μ ε z w = LQGMetric.lgdDZZ μ (Real.sqrt ε) z w := by
    rw [← liouvilleGraphDistance_sq_eq_lgdDZZ, Real.sq_sqrt hε.le]
  have hl : Real.log ε⁻¹ = 2 * Real.log (Real.sqrt ε)⁻¹ := by
    simp only [Real.log_inv, Real.log_sqrt hε.le]
    ring
  simp only [Function.comp_apply, hd, hl]
  ring

end HarmonicBalls
