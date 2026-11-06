import HarmonicBalls.Proofs.Sec6.SizeRatioSingularWeight

/-! # Oscillation of the singular Weyl weight on cone annuli -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Points in the separated annulus have norms within a factor 1201. -/
theorem norm_le_of_mem_cone_annulus {r : ℝ} {z x y : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hx : x ∈ annulus z r (6 * r)) (hy : y ∈ annulus z r (6 * r)) :
    0 < ‖x‖ ∧ ‖y‖ ≤ 1201 * ‖x‖ := by
  have hx0 : r / 100 ≤ ‖x‖ := by
    simpa [dist_zero_left] using hd.trans (infDist_le_dist_of_mem hx)
  have hxz : dist x z < 6 * r := mem_ball.1 hx.1
  have hyz : dist y z < 6 * r := mem_ball.1 hy.1
  have hxy : dist y x < 12 * r := by
    have h := dist_triangle y z x
    rw [dist_comm z x] at h
    linarith
  have hn : ‖y‖ ≤ ‖x‖ + dist y x := by
    simpa [dist_zero_right, dist_comm y x, add_comm] using dist_triangle y x (0 : ℂ)
  constructor <;> linarith

/-- The singular power weight oscillates by at most `1201 ^ |e|` on the
separated annulus. -/
theorem rpow_norm_le_of_mem_cone_annulus {r e : ℝ} {z x y : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hx : x ∈ annulus z r (6 * r)) (hy : y ∈ annulus z r (6 * r)) :
    ‖x‖ ^ e ≤ (1201 : ℝ) ^ |e| * ‖y‖ ^ e := by
  obtain ⟨hx0, hyx⟩ := norm_le_of_mem_cone_annulus hr hd hx hy
  obtain ⟨hy0, hxy⟩ := norm_le_of_mem_cone_annulus hr hd hy hx
  have hratio : ‖x‖ ^ e / ‖y‖ ^ e = (‖x‖ / ‖y‖) ^ e := by
    rw [Real.div_rpow hx0.le hy0.le]
  have hb : (‖x‖ / ‖y‖) ^ e ≤ (1201 : ℝ) ^ |e| := by
    by_cases he : 0 ≤ e
    · rw [abs_of_nonneg he]
      exact Real.rpow_le_rpow (div_nonneg hx0.le hy0.le) ((div_le_iff₀ hy0).2 hxy) he
    · have he' : 0 ≤ -e := by linarith
      have heq := Real.rpow_neg_eq_inv_rpow (‖x‖ / ‖y‖) (-e)
      simp only [neg_neg, inv_div] at heq
      rw [abs_of_nonpos (le_of_not_ge he), heq]
      exact Real.rpow_le_rpow (div_nonneg hy0.le hx0.le) ((div_le_iff₀ hx0).2 hyx) he'
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hy0 e)).1
  rw [hratio]
  exact hb

end HarmonicBalls

#print axioms HarmonicBalls.rpow_norm_le_of_mem_cone_annulus
