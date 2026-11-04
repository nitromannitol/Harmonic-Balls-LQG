import HarmonicBalls.Steps.Sec5.ScaleInvariance
import HarmonicBalls.Proofs.Sec9.BoundaryRadii
import HarmonicBalls.Draft.Section8

/-!
# Boundary nullity under changes of scale

The normalized pullback measure in Lemma 5.7 is a positive multiple of a
pushforward by a homeomorphism. Boundary nullity transfers through that map
without requiring a separate measurability assertion for the cluster family.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal Pointwise

universe u

/-- Boundary mass of a set vanishes exactly when the boundary mass of its
homeomorphic image vanishes for the corresponding positive pullback measure. -/
theorem measure_frontier_image_eq_zero_iff
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) {c : ℝ≥0∞} (hc : c ≠ 0) (S : Set X) :
    (c • μ.map e) (frontier (e '' S)) = 0 ↔ μ (frontier S) = 0 := by
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply e.continuous.measurable
    isClosed_frontier.measurableSet, ← e.image_frontier, e.injective.preimage_image]
  exact mul_eq_zero.trans (or_iff_right hc)

/-- Boundary nullity transfers from the normalized pullback measure to the
original measure at any positive scale. -/
theorem normalizedPullbackMeasure_frontier_eq_zero_iff
    (γ α₀ k : ℝ) (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ) (μ : Measure ℂ) (S : Set ℂ) :
    normalizedPullbackMeasure γ α₀ k hcirc μ (frontier (k⁻¹ • S)) = 0 ↔
      μ (frontier S) = 0 := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero (k⁻¹ : ℝ) (inv_ne_zero hk.ne')
  have hc : ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k +
      fieldCircleAverage α₀ hcirc k 0)))⁻¹ ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (inv_pos.mpr (Real.exp_pos _))).ne'
  have h := measure_frontier_image_eq_zero_iff e μ hc S
  simpa only [normalizedPullbackMeasure, e, Homeomorph.smulOfNeZero_apply, image_smul] using h

/-- The simultaneous unit-disc boundary-nullity event transfers to a disc of
radius `k`, provided the pathwise scaling identity holds for every centre and
positive mass. -/
theorem clusterBoundaryNull_of_normalized_scale
    (γ α₀ k : ℝ) (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ) (μ : Measure ℂ)
    (hunit : ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t) ⊆ ball 0 1 →
      normalizedPullbackMeasure γ α₀ k hcirc μ
        (frontier (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t)) = 0)
    (hscale : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t =
        k⁻¹ • cluster μ k (k • z)
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * t)) :
    ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) k,
      closure (cluster μ k z t) ⊆ ball 0 k → μ (frontier (cluster μ k z t)) = 0 := by
  intro t ht z hz hcl
  let A : ℝ := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hA : 0 < A := Real.exp_pos _
  have hball : (k⁻¹ : ℝ) • ball (0 : ℂ) k = ball 0 1 := by
    rw [_root_.smul_ball (inv_ne_zero hk.ne')]
    simp [Real.norm_eq_abs, abs_of_pos hk, hk.ne']
  have hz' : k⁻¹ • z ∈ ball (0 : ℂ) 1 := by
    rw [← hball]
    exact smul_mem_smul_set hz
  have hzscale : k • (k⁻¹ • z) = z := by simp [hk.ne']
  have htscale : A * (t / A) = t := by field_simp
  have heq := hscale (k⁻¹ • z) hz' (t / A) (div_pos ht hA)
  rw [hzscale, htscale] at heq
  have hcl' : closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1
      (k⁻¹ • z) (t / A)) ⊆ ball 0 1 := by
    rw [heq, closure_smul₀' (inv_ne_zero hk.ne'), ← hball]
    exact smul_set_mono hcl
  have hnull := hunit (t / A) (div_pos ht hA) (k⁻¹ • z) hz' hcl'
  rw [heq] at hnull
  exact (normalizedPullbackMeasure_frontier_eq_zero_iff γ α₀ k hk hcirc μ _).1 hnull

/-- The unit-disc event in Proposition 8.1, regarded as a property of the
measure. Its measurability is a separate obligation when transferring its law. -/
def compactClusterBoundaryNullEvent : Set (Measure ℂ) :=
  {μ | ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
    closure (cluster μ 1 z t) ⊆ ball 0 1 → μ (frontier (cluster μ 1 z t)) = 0}

/-- Unit-disc boundary nullity extends to all integer radii given the
normalized measure law, simultaneous pathwise scaling, and measurability of
the unit-disc event. -/
theorem clusterBoundaryNullIntegerRadii_of_scale
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hlaw : NormalizedPullbackMeasureLawStep.{u}) (hscale : ClusterPathwiseScaleStep.{u})
    (hmeas : MeasurableSet compactClusterBoundaryNullEvent) :
    ClusterBoundaryNullIntegerRadii.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  rw [ae_all_iff]
  intro n
  by_cases hn : 0 < n
  · have hk : 0 < (n : ℝ) := by exact_mod_cast hn
    have hunit : ∀ᵐ ω ∂P, μ ω ∈ compactClusterBoundaryNullEvent :=
      h8 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    have hscaled := (hlaw γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hk).ae_snd hmeas hunit
    filter_upwards [hscaled, hscale γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hk] with ω hu hs _
    exact clusterBoundaryNull_of_normalized_scale γ α₀ n hk (hcirc ω) (μ ω) hu hs
  · exact Filter.Eventually.of_forall fun _ h => (hn h).elim

/-- Weak Proposition 9.2 from the unit-disc boundary theorem and the
scale-change obligations listed in `clusterBoundaryNullIntegerRadii_of_scale`. -/
theorem subharmonicBallUniquenessWeak_of_unitBoundary
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hlaw : NormalizedPullbackMeasureLawStep.{u}) (hscale : ClusterPathwiseScaleStep.{u})
    (hmeas : MeasurableSet compactClusterBoundaryNullEvent) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_integerRadii hI2
    (clusterBoundaryNullIntegerRadii_of_scale h8 hlaw hscale hmeas)

end HarmonicBalls
