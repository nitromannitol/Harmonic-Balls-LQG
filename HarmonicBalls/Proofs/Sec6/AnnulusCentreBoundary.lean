import HarmonicBalls.Proofs.Sec6.CriterionThreeLatticeApprox
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-! # Boundary obstruction for changing annulus centres

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open Metric Set Filter

/-- Even an arbitrarily small positive change of centre can move points of
an annulus across its inner boundary. The outer radius here is one. -/
theorem root_annulus_not_subset_nearby_annulus {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ¬ annulus (0 : ℂ) (1 / 2) 1 ⊆ annulus (δ : ℂ) (1 / 2) 1 := by
  intro hsub
  let x : ℂ := ((1 / 2 + δ / 2 : ℝ) : ℂ)
  have hx : x ∈ annulus (0 : ℂ) (1 / 2) 1 := by
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    dsimp [x]
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    constructor <;> linarith
  have hx' := hsub hx
  simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx'
  have heq : dist x (δ : ℂ) = |1 / 2 - δ / 2| := by
    dsimp [x]
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    ring
  rw [heq, abs_of_pos (by linarith)] at hx'
  linarith [hx'.2]

/-- At every sufficiently fine criterion-three lattice mesh, the same
boundary obstruction contains an actual lattice point. -/
theorem eventually_root_lattice_not_in_nearby_annulus {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∃ x ∈ scaledLattice (dyadicScale n / 100),
      x ∈ annulus (0 : ℂ) (1 / 2) 1 ∧ x ∉ annulus (δ : ℂ) (1 / 2) 1 := by
  let y : ℂ := ((1 / 2 + δ / 2 : ℝ) : ℂ)
  have hy0 : dist y (0 : ℂ) = 1 / 2 + δ / 2 := by
    dsimp [y]
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hyδ : dist y (δ : ℂ) = 1 / 2 - δ / 2 := by
    dsimp [y]
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show 1 / 2 + δ / 2 - δ = 1 / 2 - δ / 2 by ring]
    exact abs_of_pos (by linarith)
  have hsmall : ∀ᶠ n : ℕ in atTop, dyadicScale n < δ / 4 :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by linarith))
  filter_upwards [hsmall] with n hn
  obtain ⟨x, hxlat, hxy⟩ := exists_scaledLattice_dist_lt y (δ := dyadicScale n / 100)
    (div_pos (dyadicScale_pos n) (by norm_num))
  have hclose : dist y x < δ / 4 := by linarith
  have hupper := dist_triangle x y (0 : ℂ)
  have hlower := dist_triangle y x (0 : ℂ)
  have hshift := dist_triangle x y (δ : ℂ)
  rw [dist_comm x y] at hupper hshift
  rw [hy0] at hupper hlower
  rw [hyδ] at hshift
  refine ⟨x, hxlat, ?_, ?_⟩
  · simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith
  · simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, not_and]
    intro _ hbad
    linarith

end HarmonicBalls.Section6
