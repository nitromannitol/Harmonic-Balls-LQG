import HarmonicBalls.Proofs.Sec10.JordanScaling
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec5.NoEntryPropagation
import HarmonicBalls.Proofs.Sec9.AffinePairingCovariance
import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation

/-! # Jordan boundaries via dyadic scaling -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- The unit-disc Jordan event transfers to each dyadic disc using the GFF
    affine law and the dyadic definition of the LQG measure. -/
theorem ae_clusterJordan_dyadic
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
      ∀ z ∈ ball (0 : ℂ) ((2 : ℝ) ^ m),
        closure (cluster (μ ω) ((2 : ℝ) ^ m) z t) ⊆ ball 0 ((2 : ℝ) ^ m) →
        ∀ C ∈ connectedComponentsIn (closure (cluster (μ ω) ((2 : ℝ) ^ m) z t))ᶜ,
          IsSimpleLoop (frontier C) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ m
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  let hC' := affinePairing hC hcirc (k : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (k * r) (k • z) - hcirc ω k 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hk]
    rw [hcirc_eq]
    exact hGFF.complex_affine (by exact_mod_cast hk.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback_dyadic hGFF hγ.ne' hμ m
  have hunit := h10 γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk
  filter_upwards [hunit, hscale] with ω hu hs
  exact clusterJordan_of_normalized_scale γ α₀ k hk (hcirc ω) (μ ω) hu hs

/-- Volume growth and the unit-disc Jordan event give the fixed-radius event;
    compatibility transfers it from a larger dyadic disc. -/
theorem clusterJordanFixedRadius_of_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u}) :
    ClusterJordanFixedRadius.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ r hr
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  have hk : 0 < (2 : ℝ) ^ m := by positivity
  filter_upwards [ae_clusterJordan_dyadic h10 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ m,
    clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ _ hk] with ω hj hc
  intro t ht z hz hcl C hC
  have heq := hc t ht r hm.le z hz r ⟨le_rfl, hm.le⟩ hcl _ ⟨hm.le, le_rfl⟩
  have hz' : z ∈ ball (0 : ℂ) ((2 : ℝ) ^ m) := ball_subset_ball hm.le hz
  have hcl' : closure (cluster (μ ω) ((2 : ℝ) ^ m) z t) ⊆ ball 0 ((2 : ℝ) ^ m) := by
    rw [heq]
    exact hcl.trans (ball_subset_ball hm.le)
  have hC' : C ∈ connectedComponentsIn (closure (cluster (μ ω) ((2 : ℝ) ^ m) z t))ᶜ := by
    rw [heq]
    exact hC
  exact hj t ht z hz' hcl' C hC'

/-- Proposition 10.7 follows from volume growth, existence of harmonic balls,
    and Proposition 10.6, without a general coordinate-change hypothesis. -/
theorem harmonicBallComplementBoundaryJordan_of_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u}) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_fixedRadius hI2 hexists
    (clusterJordanFixedRadius_of_dyadic hI2 h10)

end HarmonicBalls
