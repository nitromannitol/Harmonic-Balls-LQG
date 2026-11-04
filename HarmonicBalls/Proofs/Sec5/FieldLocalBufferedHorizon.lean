import HarmonicBalls.Proofs.Sec5.BufferedUniformFailure
import HarmonicBalls.Proofs.Sec5.LocalClusterFamily
import HarmonicBalls.Proofs.Sec5.UniformContainment

/-! # A field-local uniform buffered horizon -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

universe u

/-- There is a field-local measurable positive horizon before which all
clusters centred in the half-disc remain inside the fixed buffered disc.
The regularized clusters also satisfy their local harmonic-ball conditions.
The LQG measure locality hypothesis is a proposed input. -/
theorem exists_fieldLocal_uniform_buffered_horizon
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → ℝ, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, 0 < H ω ∧
        (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (H ω),
          closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 (3 / 4)) ∧
        ∀ z ∈ ball (0 : ℂ) (1 / 2),
          SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z (H ω) ∧
          ∀ t ∈ Ioo (0 : ℝ) (H ω), closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
            μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  obtain ⟨e, H, _, _, hH⟩ := exists_measurable_bufferedClusterHorizon
  obtain ⟨F, hF, heq⟩ := exists_local_lqg_clusterFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc zero_lt_one
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  let K : Ω → ℕ → Ioi (0 : ℝ) → Set ℂ := fun ω i t => F ω (e' i, t)
  have hK : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] K := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 1)
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro t
    exact (measurable_pi_apply (e' i, t)).comp hF
  let L : Ω → ℝ := fun ω => realDenseSequenceBallHorizon (3 / 4) (K ω)
  have hL : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] L :=
    (measurable_realDenseSequenceBallHorizon (ι := ℕ) (3 / 4)).comp hK
  refine ⟨L, hL, ?_⟩
  have hbase := ae_bufferedClusterHorizon_of_volumeGrowth hI2
    (clusterOpenLaplacian_proved hI2) (clusterMonotone_proved hI2)
    hγ hγ2 hα hGFF hμ e H hH
  have hpos := ae_countableCentresHorizon_pos_of_upperBound hGFF hγ hγ2 hα hμ h71 e
  have hproperties := ae_uniformLocalClusterProperties_of_containment hGFF hγ hγ2 hα hμ
    (clusterOpenLaplacian_proved hI2) h53 h54
  filter_upwards [hbase, heq, hpos, hproperties] with ω hbaseω heqω hposω hpropω
  have hident : L ω = H (μ ω) := by
    rw [hbaseω.2]
    dsimp only [L, K]
    rw [heqω]
  have hbuf : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (L ω),
      closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 (3 / 4) := by
    rw [hident]
    exact hbaseω.1
  have hp : 0 < L ω := by
    rw [hident, hbaseω.2]
    exact hposω
  refine ⟨hp, hbuf, hpropω (L ω) hp ?_⟩
  intro z hz t ht
  exact (hbuf z hz t ht).trans (closedBall_subset_ball (by norm_num))

end HarmonicBalls
