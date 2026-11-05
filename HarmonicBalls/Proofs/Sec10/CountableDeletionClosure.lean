import HarmonicBalls.Proofs.Sec10.CountableDeletionCrossingBounds

/-! # Cluster closures after countable domain deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Volume growth ensures that deleting a relatively closed countable subset of
 a disc leaves the closure of each cluster unchanged. -/
theorem closure_clusterOn_disc_sdiff_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hleq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hw' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [hleq, supersolutionsOn_ball μ hR.ne']
    exact hw
  have hcontain : closure (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) (R + 1) :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  have hopen : IsOpen (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hR hV hz.1 ht
  have hopen' : IsOpen (clusterOn μ (ball (0 : ℂ) R) z t) := by
    rwa [clusterOn_ball μ hR.ne']
  have h := closure_clusterOn_sdiff_of_relative_countable hμ
    isOpen_ball isBounded_ball hcontain hD hK
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le hz hw' hopen'
  simpa only [clusterOn_ball μ hR.ne'] using h

/-- I2 gives simultaneous closure equality over discs, poles, masses, and
relatively closed countable deletions on a single almost-sure event. -/
theorem ae_closure_clusterOn_disc_sdiff_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ K : Set ℂ,
      IsOpen (ball (0 : ℂ) R \ K) → (K ∩ ball (0 : ℂ) R).Countable →
      ∀ z ∈ ball (0 : ℂ) R \ K,
      closure (clusterOn (μ ω) (ball (0 : ℂ) R \ K) z t) =
        closure (cluster (μ ω) R z t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  intro R t hR ht K hD hK z hz
  exact closure_clusterOn_disc_sdiff_of_volumeGrowth hV.1 hR (hV.2 R hR)
    K hD hK hz ht

/-- The selected-radius crossing bound applies when compact containment is
stated directly for the punctured-domain cluster. -/
theorem ae_crossings_after_countable_deletion_of_punctured_compact_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ K : Set ℂ,
        IsOpen (ball (0 : ℂ) 1 \ K) → (K ∩ ball (0 : ℂ) 1).Countable →
        ∀ z ∈ ball (0 : ℂ) 1 \ K,
        closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆ ball 0 1 →
        (crossingComponents (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∩
          ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_after_countable_deletion_of_dyadic_scaling hI2 h66 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_closure_clusterOn_disc_sdiff_of_volumeGrowth hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hbound heq
  filter_upwards [hbound] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, ?_⟩
  intro t ht K hD hK z hz hcompact
  apply hρbound t ht K hD hK z hz
  rw [← heq 1 t zero_lt_one ht K hD hK z hz]
  exact hcompact

end HarmonicBalls
