import HarmonicBalls.Proofs.Sec10.HoleExitTimeDomination

/-! # Null sets of hole exit times

On an interval of compact containment, a Lebesgue-null set of times can
capture only a Liouville-null set of points from an initial bounded hole.
The null set of times need not itself be measurable. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Almost surely, the points of any bounded initial hole whose exit times
belong to a Lebesgue-null set inside a compact-containment time window have
zero Liouville mass. The assertion is simultaneous for all null time sets. -/
theorem ae_cluster_holeExitTime_null_preimage
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ T : ℝ, t < T →
      closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
      ∀ N : Set ℝ, volume N = 0 →
      μ ω {x | x ∈ U ∧
        holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x ∈ N ∧
        t < holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x ∧
        holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x < T} = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_pushforward_restrict_le_volume hI2 hvolume h61 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_lowerSemicontinuous_clusterHoleExitTime hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hdom hlsc
  intro t ht z hz U hU hUb T htT hclT N hN
  obtain ⟨M, hNM, hM, hMzero⟩ := exists_measurable_superset_of_null hN
  let τ := holeExitTime (fun s => closure (cluster (μ ω) 1 z s))
  have hmeas : Measurable τ := (hlsc z hz).measurable
  have hzero : (Measure.map τ ((μ ω).restrict U)).restrict (Ioo t T) M = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ volume M := (hdom t ht z hz U hU hUb T htT hclT) M
      _ = 0 := hMzero
  rw [Measure.restrict_apply hM, Measure.map_apply hmeas (hM.inter measurableSet_Ioo),
    Measure.restrict_apply (hmeas (hM.inter measurableSet_Ioo))] at hzero
  apply measure_mono_null _ hzero
  intro x hx
  exact ⟨⟨hNM hx.2.1, hx.2.2⟩, hx.1⟩

end HarmonicBalls
