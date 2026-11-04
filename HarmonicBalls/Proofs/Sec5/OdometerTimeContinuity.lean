import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability
import HarmonicBalls.Proofs.Sec3.Basic

/-!
# Time stability of the odometer away from the pole

The obstacle comparison bounds the change in the odometer by the time
increment times the Green function. On compact sets avoiding the pole this
is a uniform Lipschitz estimate, including on the boundary of the disc.
This alone does not establish continuity of the positivity sets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Increasing the time by `t - s` increases the odometer by at most
`(t - s)` times the Green function. -/
theorem odometer_sub_le_time_sub_mul_greenFunction
    {μ : Measure ℂ} {r s t : ℝ} {z x : ℂ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    odometer μ r z t x - odometer μ r z s x ≤
      (t - s) * greenFunction (ball 0 r) z x := by
  have h := leastSupersolution_antitone_time (μ := μ) (r := r) (z := z) (x := x)
    hs hst hx hxz
  dsimp only [odometer]
  nlinarith

/-- Under volume growth, the odometer is monotone and its increment is
bounded by the corresponding increment of the Green obstacle. -/
theorem odometer_time_increment_bounds
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) {z x : ℂ}
    (hz : z ∈ ball (0 : ℂ) r) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    0 ≤ odometer μ r z t x - odometer μ r z s x ∧
      odometer μ r z t x - odometer μ r z s x ≤
        (t - s) * greenFunction (ball 0 r) z x := by
  have hmono := (obstacleMonotoneGeneral_holds μ hμ r βm βp hr hV z hz s t hs hst).1 x hx hxz
  have heq1 := (obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr hV z hz s hs).2.2.2 hx
  have heq2 := (obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr hV z hz t (hs.trans_le hst)).2.2.2 hx
  refine ⟨?_, odometer_sub_le_time_sub_mul_greenFunction hs.le hst hx hxz⟩
  linarith

/-- On a compact part of the closed disc avoiding the pole, the odometer is
uniformly Lipschitz in positive time. -/
theorem odometer_uniform_lipschitz_time_on_compact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r) {K : Set ℂ} (hK : IsCompact K)
    (hKball : K ⊆ closedBall (0 : ℂ) r) (hKz : z ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ s t : ℝ, 0 < s → 0 < t →
      |odometer μ r z t x - odometer μ r z s x| ≤ C * |t - s| := by
  have hKsub : K ⊆ ({z} : Set ℂ)ᶜ := by
    intro x hx hxz
    exact hKz (by simpa only [mem_singleton_iff] using hxz ▸ hx)
  obtain ⟨C, hC⟩ := hK.bddAbove_image ((continuousOn_greenFunction_ball hz).mono hKsub)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x hx s t hs ht
  have hG : greenFunction (ball 0 r) z x ≤ max C 0 :=
    (hC ⟨x, hx, rfl⟩).trans (le_max_left C 0)
  have hxz : x ≠ z := fun h => hKz (h ▸ hx)
  rcases le_total s t with hst | hts
  · obtain ⟨hlow, hupp⟩ := odometer_time_increment_bounds hμ hr hV hz (hKball hx) hxz hs hst
    rw [abs_of_nonneg hlow, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact hupp.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr hst))
  · obtain ⟨hlow, hupp⟩ := odometer_time_increment_bounds hμ hr hV hz (hKball hx) hxz ht hts
    rw [abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp hlow)), abs_of_nonpos (sub_nonpos.mpr hts)]
    have h := hupp.trans (mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr hts))
    linarith

end HarmonicBalls
