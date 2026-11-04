import HarmonicBalls.Proofs.Sec9.SubharmonicUniqueness
import HarmonicBalls.Proofs.Sec9.DominatedGreenPotential

/-! # The supersolution associated with a subharmonic ball -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- The negative Green potential of a subharmonic ball is a supersolution for its mass. -/
theorem IsSubharmonicBall.neg_greenPotential_mem_supersolutions
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp) (hcl : closure A ⊆ ball 0 R) (hmass : μ.real A = t) :
    (fun x => -∫ y in A, greenFunction (ball 0 R) y x ∂μ) ∈ supersolutions μ R z t := by
  have hsub : A ⊆ ball (0 : ℂ) R := subset_closure.trans hcl
  have hrest : (μ.restrict A).restrict (ball 0 R) = μ.restrict A := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hsub]
  obtain ⟨hc, hΔ⟩ := dominated_greenPotentialBall hμ hR hV (Measure.restrict_le_self (s := A))
  rw [hrest] at hc hΔ
  have heqp : greenPotentialBall (μ.restrict A) R =
      fun x => ∫ y in A, greenFunction (ball 0 R) y x ∂μ := by
    funext x
    simp only [greenPotentialBall, Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hsub]
  rw [heqp] at hc hΔ
  refine ⟨hc.neg, ⟨hΔ.1.neg, ?_⟩, ?_⟩
  · intro φ hφ hφ0 hi
    obtain ⟨_, _, heq⟩ := hΔ.2 φ hφ
    have hle := integral_mono_measure (Measure.restrict_le_self (s := A))
      (Filter.Eventually.of_forall hφ0) hi
    have hneg : (fun x => (-∫ y in A, greenFunction (ball 0 R) y x ∂μ) * Δ φ x) =
        -(fun x => (∫ y in A, greenFunction (ball 0 R) y x ∂μ) * Δ φ x) := by
      funext x
      simp only [Pi.neg_apply, neg_mul]
    rw [hneg, integral_neg', heq]
    simp only [integral_zero_measure, zero_sub, neg_neg]
    exact hle
  · intro x hx hxz
    by_cases hxball : x ∈ ball (0 : ℂ) R
    · have hle := hA.greenPotential_le_of_steps greenFunctionBallSymmetric
        negGreenFunctionMemSubharmonicBallTestClass hcl hxball hxz
      have hint : ∫ y in A, greenFunction (ball 0 R) y x ∂μ = ∫ y in A, greenFunction (ball 0 R) x y ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R y x)
      change -t * greenFunction (ball 0 R) z x ≤ -∫ y in A, greenFunction (ball 0 R) y x ∂μ
      rw [hint, greenFunction_ball_comm R z x]
      rw [hmass] at hle
      linarith
    · have hG : ∀ y, greenFunction (ball 0 R) y x = 0 := by
        intro y
        simp [greenFunction, hxball]
      simp [hG]

/-- Under volume growth, the cluster of the mass of a subharmonic ball is contained in it. -/
theorem IsSubharmonicBall.cluster_subset_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hV : VolumeGrowth μ R βm βp) (hcl : closure A ⊆ ball 0 R)
    (hmass : μ A = ENNReal.ofReal t) : cluster μ R z t ⊆ A := by
  have hreal : μ.real A = t := by
    rw [measureReal_def, hmass, ENNReal.toReal_ofReal ht.le]
  exact hA.cluster_subset_of_neg_greenPotential_mem_supersolutions hcl hreal
    (hA.neg_greenPotential_mem_supersolutions hμ hR hV hcl hreal)

/-- The deterministic form of weak Proposition 9.2, given openness and mass conservation. -/
theorem IsSubharmonicBall.weak_uniqueness_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hV : VolumeGrowth μ R βm βp) (hcl : closure A ⊆ ball 0 R)
    (hmass : μ A = ENNReal.ofReal t) (hopen : IsOpen (cluster μ R z t))
    (hcluster : μ (cluster μ R z t) = ENNReal.ofReal t) :
    cluster μ R z t ⊆ A ∧ μ (A \ regularizedCluster μ R z t) = 0 := by
  have hsub := hA.cluster_subset_of_volumeGrowth hμ hR ht hV hcl hmass
  refine ⟨hsub, measure_sdiff_regularizedCluster_eq_zero hopen hsub ?_ ?_⟩
  · exact hmass.trans hcluster.symm
  · rw [hcluster]
    exact ENNReal.ofReal_ne_top

end HarmonicBalls
