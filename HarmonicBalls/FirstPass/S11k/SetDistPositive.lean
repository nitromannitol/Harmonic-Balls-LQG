import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-!
# Positivity of the boundary distance `D(∂B_δ, ∂B_{2δ})`

For a Euclidean length metric `D` (`IsEuclideanLengthMetric`, `Defs/LQGMetric.lean:81`) the distance between the disjoint
compact circles `∂B_δ(0)` and `∂B_{2δ}(0)` is positive. This gives the positivity `0 < d` on the exterior event of
Lemma 11.16 (corrected paper, proof of `lemma:E2`, lines 3700-3727): the level `c₁ ≤ D(∂B_δ, ∂B_{2δ})` of
`PinchSecondExteriorEventStep` is chosen on a set where this distance is positive. Deterministic, no input.
-/

namespace HarmonicBalls

open Metric Set

namespace IsEuclideanLengthMetric

/-- A Euclidean length metric is nonnegative (from `D z z = 0`, symmetry and the triangle inequality). -/
theorem nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have h1 := hD.triangle x y x
  have h2 := hD.symm x y
  have h3 := hD.self_eq_zero x
  linarith

/-- The distance of a Euclidean length metric is jointly continuous for the Euclidean topology: its restriction to
`univ × univ` is the continuous internal metric of `univ`, composed with `ENNReal.toReal`. -/
theorem continuous_pair {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) :
    Continuous fun p : ℂ × ℂ => D p.1 p.2 := by
  have hc := hD.continuousOn_internalMetric_pair hD.nonneg isOpen_univ
  rw [Set.univ_prod_univ, continuousOn_univ] at hc
  have hfun : (fun p : ℂ × ℂ => D p.1 p.2) =
      fun p => (internalMetric D univ p.1 p.2).toReal := by
    funext p
    rw [← hD.ofReal_eq_internalMetric, ENNReal.toReal_ofReal (hD.nonneg _ _)]
  rw [hfun]
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hfin : internalMetric D univ p.1 p.2 ≠ ⊤ := by
    rw [← hD.ofReal_eq_internalMetric]
    exact ENNReal.ofReal_ne_top
  exact ContinuousAt.comp (f := fun q : ℂ × ℂ => internalMetric D univ q.1 q.2) (x := p)
    (ENNReal.continuousAt_toReal hfin) hc.continuousAt

end IsEuclideanLengthMetric

/-- For a Euclidean length metric and `δ > 0`, the distance `D(∂B_δ(0), ∂B_{2δ}(0))` is strictly positive: the two
circles are disjoint and compact, so the continuous function `D` attains its minimum on their product at a point of
positive value. -/
theorem setDist_sphere_two_pos {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ) :
    0 < setDist D (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ)) := by
  unfold setDist
  have hK : IsCompact (sphere (0 : ℂ) δ ×ˢ sphere (0 : ℂ) (2 * δ)) :=
    (isCompact_sphere (0 : ℂ) δ).prod (isCompact_sphere (0 : ℂ) (2 * δ))
  have hne : (sphere (0 : ℂ) δ ×ˢ sphere (0 : ℂ) (2 * δ)).Nonempty := by
    have e1 : ‖((δ : ℝ) : ℂ)‖ = δ := by rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have e2 : ‖((2 * δ : ℝ) : ℂ)‖ = 2 * δ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * δ)]
    exact ⟨(((δ : ℝ) : ℂ), ((2 * δ : ℝ) : ℂ)),
      mem_sphere_zero_iff_norm.2 e1, mem_sphere_zero_iff_norm.2 e2⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hD.continuous_pair.continuousOn
  have hpos : 0 < D p.1 p.2 := by
    rcases (hD.nonneg p.1 p.2).lt_or_eq with h | h
    · exact h
    · exfalso
      have heq : p.1 = p.2 := hD.eq_of_eq_zero _ _ h.symm
      have h1 : ‖p.1‖ = δ := by simpa using hp.1
      have h2 : ‖p.2‖ = 2 * δ := by simpa using hp.2
      rw [heq] at h1
      linarith
  refine lt_of_lt_of_le hpos (le_csInf ⟨D p.1 p.2, Set.mem_image2_of_mem hp.1 hp.2⟩ ?_)
  rintro b ⟨x, hx, y, hy, rfl⟩
  exact isMinOn_iff.1 hmin (x, y) ⟨hx, hy⟩

end HarmonicBalls

