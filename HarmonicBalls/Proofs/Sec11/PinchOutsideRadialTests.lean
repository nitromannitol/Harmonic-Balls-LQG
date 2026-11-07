import HarmonicBalls.Proofs.Sec11.PinchOutsideCircleBuffers
import HarmonicBalls.Proofs.Sec11.RadialCirclePairingApproximation

/-! # Radial test functions outside the pinch core

The radial pairing approximation uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped Topology

/-- The closed core has a uniform positive radial gap from the pinning circle. -/
theorem IsCorrectedPinchConfiguration.exists_core_radial_gap
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ closure W, 1 + η ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  have hW : closure W ⊆ annulus 0 1 2 := by
    have ht : closure W ⊆ thickening (10 * δ) (closure W) :=
      self_subset_thickening (by have := h.δ₀_mem.1; positivity) _
    exact ht.trans (subset_closure.trans (h.buffer_W.trans inter_subset_right))
  have hc : IsCompact (closure W) := (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    isClosed_closure (fun x hx => by
      have hx' := (hW hx).1
      simp only [mem_ball, dist_zero_right] at hx'
      simpa only [mem_closedBall, dist_zero_right] using hx'.le)
  obtain ⟨a, ha, halower⟩ := hc.exists_forall_le' continuous_norm.continuousOn
    (a := (1 : ℝ)) (by
      intro x hx
      have hx' := (hW hx).2
      simp only [mem_closedBall, dist_zero_right, not_le] at hx'
      exact hx')
  refine ⟨a - 1, by linarith, ?_⟩
  intro x hx
  have hx' := (hW hx).1
  simp only [mem_ball, dist_zero_right] at hx'
  exact ⟨by linarith [halower x hx], hx'.le⟩

/-- At either reference radius, sufficiently narrow radial circle tests are
supported outside the closed core. -/
theorem IsCorrectedPinchConfiguration.eventually_radialAnnularTest_outside
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {r : ℝ} (hr : 0 < r) (hradii : r = 1 ∨ r = 4) :
    ∀ᶠ n : ℕ in atTop, IsTestFunction (closure W)ᶜ (radialAnnularTest r hr n) := by
  obtain ⟨η, hη, hgap⟩ := h.exists_core_radial_gap
  have he : 0 < min η 1 := lt_min hη (by norm_num)
  have hsmall := (circleDensityWidth_tendsto_zero r 1).eventually
    (Iio_mem_nhds (show (0 : ℝ) < min η 1 by exact he))
  filter_upwards [hsmall] with n hn
  let w := circleDensityWidth r 1 n
  have hw : 0 < w := circleDensityWidth_pos hr one_pos n
  have hclosed : IsClosed {x : ℂ | |‖x‖ ^ 2 - r ^ 2| ≤ w} := by
    exact isClosed_le (((continuous_norm.pow 2).sub continuous_const).abs) continuous_const
  have hts : tsupport (circleDensity r w hw 0) ⊆ {x : ℂ | |‖x‖ ^ 2 - r ^ 2| ≤ w} := by
    apply closure_minimal _ hclosed
    intro x hx
    have hx' := circleDensity_support r w hw 0 x hx
    change |‖x‖ ^ 2 - r ^ 2| ≤ w
    simpa only [sub_zero] using hx'.le
  have hout : {x : ℂ | |‖x‖ ^ 2 - r ^ 2| ≤ w} ⊆ (closure W)ᶜ := by
    intro x hx hxW
    have hg := hgap x hxW
    have hn' : w < η ∧ w < 1 := ⟨lt_of_lt_of_le hn (min_le_left _ _),
      lt_of_lt_of_le hn (min_le_right _ _)⟩
    change |‖x‖ ^ 2 - r ^ 2| ≤ w at hx
    have hx' := abs_le.mp hx
    rcases hradii with rfl | rfl <;> norm_num at hx' ⊢ <;>
      nlinarith [sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ - 2), norm_nonneg x]
  have htest := radialAnnularTest_isTestFunction hr n
  refine ⟨htest.1, htest.2.1, ?_⟩
  exact (tsupport_mul_subset_right.trans hts).trans hout

#print axioms IsCorrectedPinchConfiguration.exists_core_radial_gap
#print axioms IsCorrectedPinchConfiguration.eventually_radialAnnularTest_outside
end HarmonicBalls
