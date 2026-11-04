import HarmonicBalls.Steps.Sec11.TimeClosure
import HarmonicBalls.Steps.Sec11.TimeContinuous

/-! # First entry in a harmonic-ball family -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- For an almost-everywhere exhausting family satisfying the conditions of
Theorem 1.1, the entry-time law is Lebesgue measure on positive times, and
almost every point is a continuity point of the entry-time function and lies
on its entry frontier. -/
theorem SatisfiesHarmonicBallConditions.entry_time_law_and_frontier
    {μ : Measure ℂ} {Λ : ℝ → Set ℂ} {z : ℂ}
    (h : SatisfiesHarmonicBallConditions μ Λ z)
    (hcover : ∀ᵐ x ∂μ, ∃ t, 0 < t ∧ x ∈ Λ t) :
    let τ : ℂ → ℝ := fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}
    μ.map τ = volume.restrict (Ioi (0 : ℝ)) ∧
    (∀ᵐ x ∂μ, ContinuousAt τ x ∧ (0 < τ x → x ∈ frontier (Λ (τ x)))) := by
  dsimp only
  have hopen : ∀ t, 0 < t → IsOpen (Λ t) := fun t ht => (h.isRegularOpen t ht).isOpen
  refine ⟨map_positive_entry_time_eq_volume_of_ae_cover μ Λ hopen hcover h.monotoneOn h.measure_eq, ?_⟩
  filter_upwards [ae_continuousAt_positive_entry_time μ Λ hopen hcover h.monotoneOn h.measure_eq h.measure_frontier,
    ae_mem_frontier_at_positive_entry_of_ae_cover μ Λ hopen hcover h.monotoneOn h.measure_eq h.closure_eq_iInter]
    with x hc hf
  exact ⟨hc, hf⟩

end HarmonicBalls
