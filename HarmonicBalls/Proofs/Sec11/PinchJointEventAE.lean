import HarmonicBalls.Steps.Sec11.PinchJointEvent
import HarmonicBalls.Proofs.Sec11.PinchLocallyFiniteKernel
import HarmonicBalls.Steps.Sec11.PinchBlockMeasurable

/-! # Jointly measurable representatives of pinch events -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set

/-- An almost surely locally finite random measure and an almost surely
Euclidean length metric yield a jointly measurable pinch-event representative.
The same exceptional set works for every center. -/
theorem exists_jointlyMeasurable_pinchPointEventWithInternalBounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∃ E : Set (Ω × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ z, ((ω, z) ∈ E ↔
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M r z) := by
  obtain ⟨D', hD', hmetric', hEq⟩ := exists_measurable_lengthMetric_modification hD hmetric
  let κ := locallyFiniteRandomMeasureKernel P μ hμ
  refine ⟨{p | pinchPointEventWithInternalBounds (κ p.1) (D' p.1) U T Q' Q M r p.2},
    measurableSet_kernel_pinchPointEventWithInternalBounds κ hconfig M hr hD' hmetric', ?_⟩
  filter_upwards [hEq, ae_locallyFiniteRandomMeasureKernel_eq P μ hμ hloc] with ω hd hμω
  intro z
  change κ ω = μ ω at hμω
  simp only [hd, hμω]

/-- A countable family of scales and its eventual block-frequency event have
a jointly measurable representative on one common full-measure sample set. -/
theorem exists_jointlyMeasurable_internal_pinch_block_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M q : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∃ F : Set (Ω × ℂ), MeasurableSet F ∧
      ∀ᵐ ω ∂P, ∀ z, ((ω, z) ∈ F ↔ ∀ᶠ N : ℕ in atTop, q * N ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M (r n) z}.ncard : ℝ)) := by
  classical
  have hex (n : ℕ) := exists_jointlyMeasurable_pinchPointEventWithInternalBounds
    P hconfig M (hr n) hD hmetric hμ hloc
  let E : ℕ → Set (Ω × ℂ) := fun n => Classical.choose (hex n)
  have hE : ∀ n, MeasurableSet (E n) := fun n => (Classical.choose_spec (hex n)).1
  have hae : ∀ᵐ ω ∂P, ∀ n z, ((ω, z) ∈ E n ↔
      pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M (r n) z) :=
    ae_all_iff.mpr fun n => (Classical.choose_spec (hex n)).2
  refine ⟨{p | ∀ᶠ N : ℕ in atTop, q * N ≤
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ p ∈ E n}.ncard : ℝ)},
    measurableSet_eventually_blockEvent_ncard (fun n p => p ∈ E n) hE q, ?_⟩
  filter_upwards [hae] with ω hω
  intro z
  have hsets (N : ℕ) : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ (ω, z) ∈ E n} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M (r n) z} := by
    ext n
    simp only [mem_ofPred_eq, hω n z]
  simp only [hsets]

#print axioms exists_jointlyMeasurable_internal_pinch_block_density
#print axioms exists_jointlyMeasurable_pinchPointEventWithInternalBounds

end HarmonicBalls
