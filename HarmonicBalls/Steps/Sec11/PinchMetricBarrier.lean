import HarmonicBalls.Steps.Sec11.PinchBoundaryClearance
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-! # Metric barriers for the strengthened pinch event

A lower bound on distance from the center to the complement of the local
ball gives boundary clearance for all pairs appearing in the pinch event.
The existence or positive probability of such a barrier is not asserted.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Every path from the center to the complement of an outer ball crosses an
intermediate sphere. The two corresponding metric gaps bound its endpoint
distance from below. -/
theorem IsEuclideanLengthMetric.center_to_complement_lower_bound
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {z w : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hw : w ∉ ball z b) :
    setDist D {z} (sphere z a) + setDist D (sphere z a) (ball z b)ᶜ ≤ D z w := by
  apply (ENNReal.ofReal_le_ofReal_iff (hnonneg z w)).mp
  rw [hD.ofReal_eq_internalMetric]
  refine le_iInf fun p => le_iInf fun _ => ?_
  let f : ℝ → ℝ := fun t => dist (p.extend t) z
  have hcont : Continuous f := p.continuous_extend.dist continuous_const
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : b ≤ f 1 := by
    simpa only [f, p.extend_one, mem_ball, not_lt] using hw
  have hm : a ∈ Icc (f 0) (f 1) := ⟨by simpa [hf0] using ha, hab.trans hf1⟩
  obtain ⟨t, ht, htval⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn hm
  have htsp : p.extend t ∈ sphere z a := by simpa only [mem_sphere, f] using htval
  have hfirst := setDist_le_of_nonneg D hnonneg (mem_singleton z) htsp
  have hsecond := setDist_le_of_nonneg D hnonneg htsp
    (show w ∈ (ball z b)ᶜ from hw)
  have hseg := hD.ofReal_two_segment_le_pathLength hnonneg p ht
  calc
    ENNReal.ofReal (setDist D {z} (sphere z a) +
        setDist D (sphere z a) (ball z b)ᶜ) ≤
        ENNReal.ofReal (D z (p.extend t) + D (p.extend t) w) :=
      ENNReal.ofReal_le_ofReal (add_le_add hfirst hsecond)
    _ ≤ pathLength D p := hseg

/-- A single metric barrier around the center gives the boundary clearance
required for the two families of pairs in the strengthened pinch event. -/
theorem IsEuclideanLengthMetric.pinchBoundaryClearance_of_metric_barrier
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {T : Set ℂ} {r R : ℝ} {z : ℂ}
    (hbarrier : ∀ w ∉ ball z (6 * r), R ≤ D z w)
    (hsphere : ∀ x ∈ sphere z (5 * r), D z x < R)
    (hT : ∀ x ∈ rescaledSet T r z, ∀ y ∈ rescaledSet T r z,
      D z x + D x y < R) : PinchBoundaryClearance D T r z := by
  constructor
  · intro x hx
    exact ⟨R, hbarrier, hsphere x hx⟩
  · intro x hx y hy
    let a : ℝ := (D x y + (R - D z x)) / 2
    refine ⟨a, ?_, ?_⟩
    · intro w hw
      have htriangle := hD.triangle z x w
      have hb := hbarrier w hw
      have ht := hT x hx y hy
      dsimp [a]
      linarith
    · have ht := hT x hx y hy
      dsimp [a]
      linarith

/-- A global pinch event upgrades to the internal-bound event when the center
is protected by a metric barrier satisfying the displayed strict gaps. -/
theorem IsEuclideanLengthMetric.pinchPointEventWithInternalBounds_of_metric_barrier
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {μ : MeasureTheory.Measure ℂ}
    {U T Q' Q : Set ℂ} {M r R : ℝ} {z : ℂ}
    (hbarrier : ∀ w ∉ ball z (6 * r), R ≤ D z w)
    (hsphere : ∀ x ∈ sphere z (5 * r), D z x < R)
    (hT : ∀ x ∈ rescaledSet T r z, ∀ y ∈ rescaledSet T r z,
      D z x + D x y < R)
    (hp : pinchPointEvent μ D U T Q' Q M r z) :
    pinchPointEventWithInternalBounds μ D U T Q' Q M r z :=
  pinchPointEventWithInternalBounds_of_boundaryClearance hD hnonneg
    (hD.pinchBoundaryClearance_of_metric_barrier hbarrier hsphere hT) hp

/-- Two radial crossing distances supply the barrier used to upgrade a
global pinch event. The strict gap inequalities remain explicit. -/
theorem IsEuclideanLengthMetric.pinchPointEventWithInternalBounds_of_radial_gaps
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {μ : MeasureTheory.Measure ℂ}
    {U T Q' Q : Set ℂ} {M r : ℝ} {z : ℂ} (hr : 0 ≤ r)
    (hsphere : ∀ x ∈ sphere z (5 * r), D z x <
      setDist D {z} (sphere z (5 * r)) +
        setDist D (sphere z (5 * r)) (ball z (6 * r))ᶜ)
    (hT : ∀ x ∈ rescaledSet T r z, ∀ y ∈ rescaledSet T r z,
      D z x + D x y < setDist D {z} (sphere z (5 * r)) +
        setDist D (sphere z (5 * r)) (ball z (6 * r))ᶜ)
    (hp : pinchPointEvent μ D U T Q' Q M r z) :
    pinchPointEventWithInternalBounds μ D U T Q' Q M r z := by
  apply hD.pinchPointEventWithInternalBounds_of_metric_barrier hnonneg ?_ hsphere hT hp
  intro w hw
  exact hD.center_to_complement_lower_bound hnonneg (by positivity) (by linarith) hw

#print axioms IsEuclideanLengthMetric.pinchPointEventWithInternalBounds_of_radial_gaps
#print axioms IsEuclideanLengthMetric.center_to_complement_lower_bound
#print axioms IsEuclideanLengthMetric.pinchBoundaryClearance_of_metric_barrier
#print axioms IsEuclideanLengthMetric.pinchPointEventWithInternalBounds_of_metric_barrier

end HarmonicBalls
