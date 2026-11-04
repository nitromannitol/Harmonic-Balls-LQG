import HarmonicBalls.Proofs.Sec10.CrossingsAssembly
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator
import HarmonicBalls.Proofs.Sec9.AffinePairingCovariance
import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation

/-! # Dyadic enlargement for annular crossing bounds -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal Pointwise

universe u

/-- After enlargement to the disc of radius two, the crossing estimate holds
at all admissible unit-disc centers without a boundary margin. The factor-two
pullback is obtained from the dyadic LQG limit. -/
theorem ae_crossings_no_margins_of_dyadic_scaling
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_pole_avoiding_crossings_at_good_radius hI2 h69 h66 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hGFF.complex_affine (by norm_num : (2 : ℂ) ≠ 0) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) := by
    simpa only [pow_one, hcirc'] using
      isLQGMeasureOfField_normalizedPullback_dyadic hGFF hγ.ne' hμ 1
  have hunit := hbound α₀ hα₀ Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  have hcompat := clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  filter_upwards [hunit, hscale, hcompat] with ω hunit hscale hcompat
  have htend : Tendsto (fun ε : ℝ => ε / 4) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuous_id.div_const 4).tendsto (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε / 4
      exact div_pos (show 0 < ε from hε) (by norm_num)
  filter_upwards [htend.eventually hunit,
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hunit hεsmall hε
  apply crossings_of_larger_disc_normalization_no_pole_margin (μ ω)
    (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω))
    (Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0)))
    α ε (Real.exp_pos _) hε hεsmall hunit hscale
  intro z hz t ht hcl
  have heq := hcompat t ht 1 (by norm_num) z hz 1 (by norm_num) hcl 2 (by norm_num)
  exact heq

/-- The same boundary-free estimate holds for all poles, since clusters
whose pole lies outside the unit disc are empty. -/
theorem ae_crossings_no_margins_all_poles_of_dyadic_scaling
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_no_margins_of_dyadic_scaling hI2 h69 h66 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  filter_upwards [hω] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · exact hρbound z hz t ht hcl
  · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
    simp [crossingComponents, connectedComponentsIn]




/-- Lemma 10.1 from I2, Lemmas 6.6 and 6.9, with no additional field-scaling inputs. -/
theorem clusterBoundedCrossings_of_prevalence_and_comparison_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u}) : ClusterBoundedCrossingsStmt.{u} := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_crossings_no_margins_all_poles_of_dyadic_scaling hI2 h69 h66 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  filter_upwards [hω] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  exact ⟨ρ, hρ, fun t ht z hcl => hρbound z t ht hcl⟩

/-- Lemma 10.1 from volume growth and annular prevalence. -/
theorem clusterBoundedCrossings_of_volumeGrowth_and_prevalence_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_prevalence_and_comparison_dyadic hI2
    (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2) h66

/-- Lemma 10.1 from volume growth, subrange prevalence, and staged LQG
existence and Weyl scaling. -/
theorem clusterBoundedCrossings_of_volumeGrowth_and_subrange_dyadic
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hsub : VeryGoodAnnuliSubRangeStep.{u})
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc) : ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_prevalence_dyadic hI2
    (manyVeryGoodAnnuliStmt_of_literature hsub hex hW)

end HarmonicBalls
