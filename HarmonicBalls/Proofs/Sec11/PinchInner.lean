import HarmonicBalls.Steps.Sec11.PinchInequalities
import HarmonicBalls.Steps.Sec11.ApproximatePaths

/-!
# The inner inclusion of Lemma 11.14

Use nearly minimizing paths and the strict diameter gap; no existence of
geodesics or properness of the metric is required.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- The pinch event places the scaled keyhole region in the metric ball whose
boundary contains `z`, for any centre outside the larger Euclidean ball. -/
theorem pinchPointEvent_keyhole_subset_metricBall
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z) (hr : 0 < r)
    (hw : w ∉ ball z (10 * r))
    (hz : z ∈ frontier (lqgMetricBall D w u)) :
    rescaledSet T r z ⊆ lqgMetricBall D w u := by
  let S : ℝ≥0∞ := ⨆ a ∈ rescaledSet T r z,
    ⨆ b ∈ rescaledSet T r z, ENNReal.ofReal (D a b)
  let b := setDist D {z} (sphere z (5 * r))
  have hS : S < ENNReal.ofReal b := hp.2.1
  have hb : 0 < b := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hS)
  have hStop : S ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hS le_top)
  have hgap : S.toReal < b := by
    have hh := (ENNReal.toReal_lt_toReal hStop ENNReal.ofReal_ne_top).2 hS
    simpa only [ENNReal.toReal_ofReal hb.le] using hh
  let ε := (b - S.toReal) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg w z hε
  have hdist : 5 * r ≤ dist w z := by
    have hh : 10 * r ≤ dist w z := le_of_not_gt hw
    linarith
  obtain ⟨t, ht, hq⟩ := path_meets_sphere_of_dist_le p (by positivity) hdist
  let q := p.extend t
  have hqT : q ∈ closure (rescaledSet T r z) :=
    sphere_subset_closure_rescaledSet hconfig hr z hq
  have hrad : b ≤ D z q := setDist_le_of_nonneg D hnonneg (Set.mem_singleton z) hq
  have hpath := lt_of_le_of_lt (hD.ofReal_two_segment_le_pathLength hnonneg p ht) hp
  have hpath' : D w q + D q z < D w z + ε :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (hnonneg w q) (hnonneg q z))).mp hpath
  intro y hy
  have hbound : D q y ≤ S.toReal := by
    apply closure_minimal (s := rescaledSet T r z) _
      (isClosed_le (hD.continuous_left y) continuous_const) hqT
    intro a ha
    change D a y ≤ S.toReal
    have haS : ENNReal.ofReal (D a y) ≤ S :=
      le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    have hh := ENNReal.toReal_mono hStop haS
    simpa only [ENNReal.toReal_ofReal (hnonneg a y)] using hh
  have htri := hD.triangle w q y
  have hu := hD.distance_eq_of_mem_frontier_ball w z u hz
  rw [hD.symm q z] at hpath'
  change D w y < u
  dsimp [ε] at hpath'
  linarith

end HarmonicBalls
