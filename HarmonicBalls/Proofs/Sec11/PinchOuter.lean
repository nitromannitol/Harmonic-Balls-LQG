import HarmonicBalls.Steps.Sec11.PinchInequalities
import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.PathCrossings

/-! # The outer inclusion of Lemma 11.14 -/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- The pinch event puts the scaled `Q'` in the complement of the metric ball
whose boundary contains `z`. The ball centre can be any point outside the
larger Euclidean ball. -/
theorem pinchPointEvent_outer_subset_compl_metricBall
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (M r u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q M r z) (hr : 0 < r)
    (hw : w ∉ ball z (10 * r))
    (hz : z ∈ frontier (lqgMetricBall D w u)) :
    rescaledSet Q' r z ⊆ (lqgMetricBall D w u)ᶜ := by
  let S : ℝ≥0∞ := ⨆ x ∈ sphere z (5 * r), ENNReal.ofReal (D z x)
  let b := setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))
  have hS : S < ENNReal.ofReal b := hp.1
  have hb : 0 < b := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hS)
  have hStop : S ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hS le_top)
  have hgap : S.toReal < b := by
    have hh := (ENNReal.toReal_lt_toReal hStop ENNReal.ofReal_ne_top).2 hS
    simpa only [ENNReal.toReal_ofReal hb.le] using hh
  let ε := (b - S.toReal) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hQball : rescaledSet Q r z ⊆ ball z (5 * r) := by
    apply rescaledSet_subset_ball _ hr z
    intro x hx
    exact (hconfig.Q_subset hx).1.1
  have hQopen : IsOpen (rescaledSet Q r z) := isOpen_rescaledSet hconfig.isOpen_Q (ne_of_gt hr) z
  have hdist : 5 * r ≤ dist w z := by
    have hh : 10 * r ≤ dist w z := le_of_not_gt hw
    linarith
  intro a ha
  have haQ : a ∈ rescaledSet Q r z := by
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨x, hconfig.closure_Q'_subset (subset_closure hx), rfl⟩
  have haball : dist a z ≤ 5 * r := le_of_lt (hQball haQ)
  obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg w a hε
  obtain ⟨s, hs, hsphere⟩ := path_meets_sphere_between p hdist haball
  have hsout : p.extend s ∉ rescaledSet Q r z := by
    intro hsQ
    have hlt : dist (p.extend s) z < 5 * r := hQball hsQ
    have heq : dist (p.extend s) z = 5 * r := hsphere
    linarith
  obtain ⟨t, ht, hfront⟩ := path_meets_frontier_after p hQopen haQ hs hsout
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hs.1 ht.1, ht.2⟩
  let q := p.extend s
  let x := p.extend t
  have hrad : D z q ≤ S.toReal := by
    have hle : ENNReal.ofReal (D z q) ≤ S := le_iSup_of_le q (le_iSup_of_le hsphere le_rfl)
    have hh := ENNReal.toReal_mono hStop hle
    simpa only [ENNReal.toReal_ofReal (hnonneg z q)] using hh
  have hsep : b ≤ D x a := by
    rw [hD.symm x a]
    exact setDist_le_of_nonneg D hnonneg ha hfront
  have hpath := lt_of_le_of_lt (hD.ofReal_three_segment_le_pathLength hnonneg p hs ht' ht.1) hp
  have hpath' : D w q + D q x + D x a < D w a + ε :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (add_nonneg (hnonneg w q) (hnonneg q x)) (hnonneg x a))).mp hpath
  have htri := hD.triangle w q z
  have hpositive := hnonneg q x
  have hu := hD.distance_eq_of_mem_frontier_ball w z u hz
  rw [hD.symm q z] at htri
  change ¬ D w a < u
  dsimp [ε] at hpath'
  linarith

end HarmonicBalls
