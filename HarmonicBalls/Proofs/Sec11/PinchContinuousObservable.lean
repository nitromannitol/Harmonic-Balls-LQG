import HarmonicBalls.Steps.Sec11.PinchLocalEvent
import HarmonicBalls.Proofs.Sec11.JointInternalBaseMetricShift

/-! # Pinch events for continuous metric-measure observations

The joint shift decoder uses Leonardo Bonanno's LatticeProb formalization. -/

namespace HarmonicBalls
open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- For a law concentrated on length metrics, the pinch event has a Borel
representative on pairs of measures and continuous distances. -/
theorem exists_pinchEvent_continuous_observable_representative
    (P : Measure (Measure ℂ × C(ℂ × ℂ, ℝ)))
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ᵐ p ∂P, IsEuclideanLengthMetric (fun x y => p.2 (x, y))) :
    ∃ E : Set (Measure ℂ × C(ℂ × ℂ, ℝ)), MeasurableSet E ∧ ∀ᵐ p ∂P,
      (pinchPointEventWithInternalBounds p.1 (fun x y => p.2 (x, y)) U T Q' Q M r z ↔ p ∈ E) := by
  let Ω := Measure ℂ × C(ℂ × ℂ, ℝ)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable S := hSc.to_subtype
  let G : Ω → ℂ → ℂ → ℝ≥0∞ := fun p x y =>
    denseClearanceChainInf S (ball z (6 * r)) (fun a b => p.2 (a, b)) x y
  have hG (x y : ℂ) : Measurable (fun p => G p x y) := by
    exact measurable_denseClearanceChainInf x y
      (fun a b => (continuous_eval_const (a, b)).measurable.comp measurable_snd)
      (fun p x => p.2.continuous.comp (continuous_const.prodMk continuous_id))
  have hGeq : ∀ᵐ p ∂P, ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric (fun a b => p.2 (a, b)) (ball z (6 * r)) x y = G p x y := by
    filter_upwards [hD] with p hp x hx y hy
    have hn (a b : ℂ) : 0 ≤ p.2 (a, b) := by
      have ht := hp.triangle a b a
      rw [hp.self_eq_zero, hp.symm b a] at ht
      linarith
    exact hp.internalMetric_eq_denseClearanceChainInf hn hSd isOpen_ball hx
  apply exists_local_pinchEvent_representative hconfig M z hr hD hG hGeq
  · exact ⟨_, (measurable_annulusGreenPotentialSup z _ _).comp measurable_fst, ae_of_all _ fun _ => rfl⟩
  · exact ⟨_, (Measure.measurable_coe
      (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet).comp measurable_fst,
      ae_of_all _ fun _ => rfl⟩

end HarmonicBalls
