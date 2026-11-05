import HarmonicBalls.Proofs.Sec10.HoleExitTimeAtoms
import HarmonicBalls.Proofs.Sec10.HoleExitExistenceAssembly

/-! # Exit-time atoms and cluster frontiers

The frontier exit theorem gives absence of atoms at every time, without a
compact-containment condition at a later time. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under the interior continuity assumptions, the mass in a bounded initial
hole with a prescribed exit time is zero. The closed cluster need not be
compactly contained in the unit disc at the exit time. -/
theorem ae_cluster_holeExitTime_mass_singleton_eq_zero_of_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ c : ℝ,
      μ ω {x | x ∈ U ∧ holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x = c} = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_on_frontier hI2 hvolume h61
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hexit hnull
  intro t ht z hz U hU hUb c
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall) hU hUb
  have hpoint : ∀ x ∈ U,
      let τ := holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x
      t < τ ∧ x ∈ frontier (cluster (μ ω) 1 z τ) := by
    intro x hx
    obtain ⟨p, hp, hpU⟩ := hU
    have hxp : x ∈ connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ p := hpU.symm ▸ hx
    have hxout : x ∈ (closure (cluster (μ ω) 1 z t))ᶜ := connectedComponentIn_subset _ _ hxp
    have heq : connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x = U :=
      (connectedComponentIn_eq hxp).symm.trans hpU
    have h := hexit t ht z hz x hxout (heq ▸ hUb)
    exact ⟨h.1, h.2.2.1⟩
  by_cases hc : 0 < c
  · apply measure_mono_null _ (hnull c hc z hz)
    intro x hx
    have h := hpoint x hx.1
    rw [hx.2] at h
    exact ⟨h.2, hUdisc hx.1⟩
  · have he : {x | x ∈ U ∧ holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x = c} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx htime
      have h := (hpoint x hx).1
      rw [htime] at h
      exact hc (ht.trans h)
    rw [he, measure_empty]

/-- The pathwise exit-time pushforward of the Liouville measure restricted to
an initial bounded hole has no atoms. -/
theorem ae_cluster_holeExitTime_pushforward_noAtoms_of_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → NullSingletonClass
        (Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s))) ((μ ω).restrict U)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_mass_singleton_eq_zero_of_frontier hI2 hvolume h61 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_lowerSemicontinuous_clusterHoleExitTime hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hatom hlsc
  intro t ht z hz U hU hUb
  refine ⟨fun c => ?_⟩
  have hm := (hlsc z hz).measurable
  rw [Measure.map_apply hm (measurableSet_singleton c),
    Measure.restrict_apply (hm (measurableSet_singleton c))]
  convert hatom t ht z hz U hU hUb c using 1
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  tauto

/-- Three staged LQG inputs and Lemma 8.2 give the pathwise non-atomic
exit-time distribution. The staged inputs await source review. -/
theorem ae_cluster_holeExitTime_pushforward_noAtoms_of_existence
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → NullSingletonClass
        (Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s))) ((μ ω).restrict U)) := by
  have hI2 := lqgVolumeGrowthAllScalesStmt_of_existence hDG hCC hE
  exact ae_cluster_holeExitTime_pushforward_noAtoms_of_frontier hI2
    (liouvilleVolumeGrowthStmt_of_existence hDG hCC hE)
    (Section6.harnackTypeEstimateStmt_of_volumeGrowth_zero_existence hI2
      (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc)) h82

end HarmonicBalls
