import HarmonicBalls.Proofs.Sec6.CircleInstantCrossing
import HarmonicBalls.Proofs.Sec6.CollarReturnTransport

/-! # Stability of circle crossings under spatial translation -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- A continuous path which visits both sides of a circle continues to cross it
under every sufficiently small spatial translation. -/
theorem exists_circle_crossing_of_small_translation
    (ω : ContinuousPath ℂ) {z : ℂ} {r : ℝ} {s t : ℝ≥0}
    (hs : dist (ω s) z < r) (ht : r < dist (ω t) z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℂ, ‖v‖ < δ →
      ∃ u : ℝ≥0, u ≤ max s t ∧ dist (ω u + v) z = r := by
  let δ := min (r - dist (ω s) z) (dist (ω t) z - r) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  have hvs : |dist (ω s + v) z - dist (ω s) z| ≤ ‖v‖ := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using abs_dist_sub_le (ω s + v) (ω s) z
  have hvt : |dist (ω t + v) z - dist (ω t) z| ≤ ‖v‖ := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using abs_dist_sub_le (ω t + v) (ω t) z
  have hδs : δ ≤ (r - dist (ω s) z) / 2 := by dsimp [δ]; linarith [min_le_left (r - dist (ω s) z) (dist (ω t) z - r)]
  have hδt : δ ≤ (dist (ω t) z - r) / 2 := by dsimp [δ]; linarith [min_le_right (r - dist (ω s) z) (dist (ω t) z - r)]
  have hs' : dist (ω s + v) z ≤ r := by have := (abs_le.mp hvs).2; linarith
  have ht' : r ≤ dist (ω t + v) z := by have := (abs_le.mp hvt).1; linarith
  have hc : Continuous (fun u : ℝ≥0 => dist (ω u + v) z) := by fun_prop
  have hr : r ∈ Set.uIcc (dist (ω s + v) z) (dist (ω t + v) z) := by
    rw [uIcc_of_le (hs'.trans ht')]
    exact ⟨hs', ht'⟩
  obtain ⟨u, hu, heq⟩ := intermediate_value_uIcc hc.continuousOn hr
  rcases mem_uIcc.mp hu with hu | hu
  · exact ⟨u, hu.2.trans (le_max_right _ _), heq⟩
  · exact ⟨u, hu.2.trans (le_max_left _ _), heq⟩

/-- Almost every Brownian path started on the circle crosses it after each
sufficiently small translation, before exiting any set containing the
translated neighborhood. -/
theorem ae_small_translation_crosses_circle_before_exit
    {z y : ℂ} {r : ℝ} (hr : 0 < r) (hy : dist y z = r)
    {V : Set ℂ} (hV : IsOpen V) (hyV : y ∈ V) :
    ∀ᵐ ω ∂planarBrownianMotion y, ∃ δ : ℝ, 0 < δ ∧
      ∀ v : ℂ, ‖v‖ < δ → ∀ U : Set ℂ, (fun w : ℂ => w + v) '' V ⊆ U →
        ∃ u : ℝ≥0, (u : ℝ≥0∞) < ContinuousPath.exitTime U
          ((⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ)).comp ω) ∧
          dist (ω u + v) z = r := by
  filter_upwards [ae_planarBrownian_visits_both_sides_before_exit hr hy hV hyV] with ω hω
  obtain ⟨⟨s, hsV, hs⟩, ⟨t, htV, ht⟩⟩ := hω
  obtain ⟨δ, hδ, hcross⟩ := exists_circle_crossing_of_small_translation ω hs ht
  refine ⟨δ, hδ, ?_⟩
  intro v hv U hVU
  obtain ⟨u, hu, heq⟩ := hcross v hv
  refine ⟨u, ?_, heq⟩
  have hmax : ((max s t : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime V ω := by
    rcases le_total s t with h | h
    · simpa only [max_eq_right h] using htV
    · simpa only [max_eq_left h] using hsV
  have htime : ContinuousPath.exitTime V ω = ContinuousPath.exitTime
      ((fun w : ℂ => w + v) '' V)
      ((⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ)).comp ω) := by
    symm
    exact exitTime_comp_injective (⟨fun w : ℂ => w + v, by fun_prop⟩ : C(ℂ, ℂ))
      (fun _ _ h => add_right_cancel h) V ω
  rw [htime] at hmax
  exact (lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hu) hmax).trans_le
    (ContinuousPath.exitTime_mono hVU _)

/-- Hitting a closed set before leaving an open set is measurable, including
when the closed set is unbounded. -/
theorem measurableSet_hit_closed_before_exit {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsClosed K) :
    MeasurableSet {ω : ContinuousPath ℂ | ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < ContinuousPath.exitTime U ω ∧ ω t ∈ K} := by
  have heq : {ω : ContinuousPath ℂ | ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < ContinuousPath.exitTime U ω ∧ ω t ∈ K} =
      {ω | ContinuousPath.exitTime Kᶜ ω < ContinuousPath.exitTime U ω} := by
    ext ω
    constructor
    · rintro ⟨t, ht, hK⟩
      exact (ContinuousPath.exitTime_le_of_notMem Kᶜ ω t (by simpa using hK)).trans_lt ht
    · intro h
      by_contra hn
      have hle : ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω := by
        rw [ContinuousPath.le_exitTime_iff]
        intro t ht
        exact le_of_not_gt (fun hlt => hn ⟨t, hlt, by simpa using ht⟩)
      exact (not_lt_of_ge hle) h
  rw [heq]
  exact measurableSet_lt (ContinuousPath.measurable_exitTime Kᶜ hK.isOpen_compl)
    (ContinuousPath.measurable_exitTime U hU)

end HarmonicBalls.Section6
