import HarmonicBalls.Steps.Sec11.PinchConstrainedWitness
import HarmonicBalls.Steps.Sec11.PinchProofAssembly
import HarmonicBalls.Steps.Sec11.BoundaryClearance
import HarmonicBalls.Steps.Sec11.PinchMetricBarrier

/-! # A metric barrier for obstacle-avoiding pinch paths

A lower bound for distance from the origin to the complement of the radius-six
ball confines sufficiently short obstacle-avoiding paths to that ball. The
existence or positive probability of the required barrier is not asserted.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- A strict uniform path-length bound below a boundary barrier allows the
radius-six restriction to be added to an obstacle-avoiding path estimate. -/
theorem IsEuclideanLengthMetric.pinchConstrainedPaths_of_barrier
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (W Q' Q : Set ℂ) (δ b : ℝ)
    (hclear : ∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w)
    (hfirst : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)))
    (hbarrier : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) < ENNReal.ofReal b) :
    (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  have hmin := lt_min hfirst hbarrier
  obtain ⟨c, hc, hpaths⟩ :=
    (iSup_internalMetric_lt_iff_exists_uniform_paths D _ _ _ _).mp hmin
  have hcfirst := hc.trans_le (min_le_left _ _)
  have hcbarrier := hc.trans_le (min_le_right _ _)
  apply (iSup_internalMetric_lt_iff_exists_uniform_paths D _ _ _ _).2
  refine ⟨c, hcfirst, ?_⟩
  intro x hx
  obtain ⟨p, hp, hlen⟩ := hpaths x hx
  have hinside := hD.path_stays_inside_of_boundary_clearance hnonneg hclear p
    (hlen.trans_lt hcbarrier)
  exact ⟨p, fun t => ⟨hp t, hinside t⟩, hlen⟩

/-- The original first auxiliary event and a sufficiently large boundary
barrier give the constrained path estimate needed by the internal event. -/
theorem IsPinchPointProofConfiguration.pinchPointEventWithInternalBounds_of_barrier
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (μ : MeasureTheory.Measure ℂ) (M b : ℝ)
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ)
    (hclear : ∀ w ∉ ball (0 : ℂ) 6, b ≤ D 0 w)
    (hbarrier : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) < ENNReal.ofReal b) :
    HarmonicBalls.pinchPointEventWithInternalBounds μ D U T Q' Q M 1 0 := by
  apply h.pinchPointEventWithInternalBounds hD hnonneg μ M hfirst hsecond hthird
  exact hD.pinchConstrainedPaths_of_barrier hnonneg W Q' Q δ b hclear hfirst.1 hbarrier

/-- Two radial metric gaps provide the barrier for the constrained paths. -/
theorem IsEuclideanLengthMetric.pinchConstrainedPaths_of_radial_gaps
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (W Q' Q : Set ℂ) (δ : ℝ)
    (hfirst : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)))
    (hgap : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
      ENNReal.ofReal (setDist D {0} (sphere 0 5) +
        setDist D (sphere 0 5) (ball 0 6)ᶜ)) :
    (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  apply hD.pinchConstrainedPaths_of_barrier hnonneg W Q' Q δ _ ?_ hfirst hgap
  intro w hw
  exact hD.center_to_complement_lower_bound hnonneg (by norm_num) (by norm_num) hw

#print axioms IsEuclideanLengthMetric.pinchConstrainedPaths_of_radial_gaps
#print axioms IsEuclideanLengthMetric.pinchConstrainedPaths_of_barrier
#print axioms IsPinchPointProofConfiguration.pinchPointEventWithInternalBounds_of_barrier

end HarmonicBalls
