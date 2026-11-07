import HarmonicBalls.Proofs.Sec11.SquareContinuitySelection
import HarmonicBalls.Proofs.Sec11.CorrectedPinchCoreGeometry

/-! # A continuity square for corrected pinch geometry -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped Topology

/-- The mass core can be chosen with almost surely null frontier for the
LQG measure while retaining the geometric buffers. -/
theorem IsCorrectedPinchConfiguration.exists_continuity_mass_core_square
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hg : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      closedSquare z L ⊆ interior (closure V) ∧
      (∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball (0 : ℂ) 3) ∧
      ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0 := by
  let : IsProbabilityMeasure P := hg.isProbabilityMeasure
  obtain ⟨z, L, hL, hSU, hfront⟩ := exists_ae_null_frontier_closedSquare_subset P μ
    (hg.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ hw => hw.isLocallyFiniteMeasure)
    h.isOpen_U h.isConnected_U.nonempty
  exact ⟨z, L, hL, hSU, hSU.trans h.closure_V_core.2.2,
    fun n x hx => h.mass_buffer n x (hSU hx), hfront⟩

#print axioms IsCorrectedPinchConfiguration.exists_continuity_mass_core_square
end HarmonicBalls
