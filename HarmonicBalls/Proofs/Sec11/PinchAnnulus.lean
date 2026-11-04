import HarmonicBalls.Proofs.Sec11.PinchMetricBall
import HarmonicBalls.Proofs.Sec11.AnnulusComparison

/-! # The deterministic contradiction in Proposition 11.11 -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A pinch event at a boundary point is incompatible with the annulus mass
bound when the set in that bound is the metric ball. -/
theorem pinchPointEvent_not_annulusMassBound
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ)
    (C r u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q C r z) (hr : 0 < r)
    (hw : w ∉ ball z (10 * r)) (hz : z ∈ frontier (lqgMetricBall D w u)) :
    ¬ ((annulus z (4 * r) (5 * r) ∩ (lqgMetricBall D w u)ᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ lqgMetricBall D w u) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r)) := by
  intro hbound
  have hTin := pinchPointEvent_keyhole_subset_metricBall μ D U T Q' Q C r u w z
    hconfig hD hnonneg hp hr hw hz
  have hQout := pinchPointEvent_outer_subset_compl_metricBall μ D U T Q' Q C r u w z
    hconfig hD hnonneg hp hr hw hz
  have hU : rescaledSet U r z ⊆ annulus z r (2 * r) ∩ lqgMetricBall D w u := by
    intro a ha
    constructor
    · have hh : a ∈ rescaledSet (annulus 0 1 2) r z := by
        obtain ⟨x, hx, rfl⟩ := ha
        exact ⟨x, hconfig.U_subset hx, rfl⟩
      simpa only [one_mul] using rescaledSet_annulus_subset 1 2 hr z hh
    · apply hTin
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hconfig.closure_U_subset (subset_closure hx), rfl⟩
  have hall := annulus_subset_of_pinchPointEvent μ D U T Q' Q (lqgMetricBall D w u)
    C r z hU hbound hp
  obtain ⟨x, hx⟩ := hconfig.isConnected_Q'.nonempty
  let y : ℂ := (r : ℂ) * x + z
  have hyQ' : y ∈ rescaledSet Q' r z := ⟨x, hx, rfl⟩
  have hxQ := hconfig.closure_Q'_subset (subset_closure hx)
  have hyann : y ∈ annulus z (4 * r) (5 * r) := by
    apply rescaledSet_annulus_subset 4 5 hr z
    exact ⟨x, (hconfig.Q_subset hxQ).1, rfl⟩
  exact hQout hyQ' (hall hyann)

/-- The annulus comparison and a pinch event rule out equality of the set
with the metric ball. This is the deterministic implication in Proposition 11.11. -/
theorem ne_metricBall_of_pinchPointEvent_and_annulusMassBound
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q Λ : Set ℂ)
    (C r u : ℝ) (w z : ℂ) (hconfig : IsPinchPointConfiguration U T Q' Q)
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (hp : pinchPointEvent μ D U T Q' Q C r z) (hr : 0 < r)
    (hw : w ∉ ball z (10 * r)) (hz : z ∈ frontier (lqgMetricBall D w u))
    (hbound : (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    Λ ≠ lqgMetricBall D w u := by
  intro heq
  subst Λ
  exact pinchPointEvent_not_annulusMassBound μ D U T Q' Q C r u w z hconfig hD hnonneg hp hr hw hz hbound

end HarmonicBalls
