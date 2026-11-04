import HarmonicBalls.Draft.Section9

/-!
# Comparison and mass reduction for Proposition 9.2

The paper's proof compares the least supersolution with a supersolution that agrees with the
obstacle outside the subharmonic ball. The mass conclusion then follows from equality of the
cluster's mass with the ball's mass and openness of the cluster.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A supersolution that equals the obstacle outside a set containing the pole forces the
cluster to lie in that set. -/
theorem cluster_subset_of_supersolution {μ : Measure ℂ} {R t : ℝ} {z : ℂ} {A : Set ℂ}
    (hz : z ∈ A) {w : ℂ → ℝ} (hw : w ∈ supersolutions μ R z t)
    (heq : ∀ x ∈ ball (0 : ℂ) R \ A, w x = -t * greenFunction (ball 0 R) z x) :
    cluster μ R z t ⊆ A := by
  intro x hx
  by_contra hxA
  rcases hx with ⟨hxball, hxz | hlt⟩
  · exact hxA (hxz ▸ hz)
  · have hxz : x ≠ z := fun h => hxA (h ▸ hz)
    have hle := leastSupersolution_le hw (ball_subset_closedBall hxball) hxz
    rw [heq x ⟨hxball, hxA⟩] at hle
    exact (not_lt_of_ge hle) hlt

/-- An open cluster contained in a set of equal finite mass leaves zero mass outside its
regularization. -/
theorem measure_sdiff_regularizedCluster_eq_zero {μ : Measure ℂ} {R t : ℝ} {z : ℂ} {A : Set ℂ}
    (hopen : IsOpen (cluster μ R z t)) (hsub : cluster μ R z t ⊆ A)
    (hmass : μ A = μ (cluster μ R z t)) (hfin : μ (cluster μ R z t) ≠ ⊤) :
    μ (A \ regularizedCluster μ R z t) = 0 := by
  have hreg : cluster μ R z t ⊆ regularizedCluster μ R z t :=
    hopen.subset_interior_iff.mpr subset_closure
  apply measure_mono_null (sdiff_subset_sdiff_right hreg)
  rw [measure_sdiff hsub hopen.measurableSet.nullMeasurableSet hfin, hmass, tsub_self]

end HarmonicBalls
