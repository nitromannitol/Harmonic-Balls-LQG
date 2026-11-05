import HarmonicBalls.Proofs.Sec10.HoleExitTimeDomination

/-! # Local domination of hole exit-time laws

On compact-containment windows, interval estimates already imply that the
restricted exit-time law is atomless. This avoids global frontier regularity
assumptions in the domination argument. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under I2 and Lemma 8.2, the exit-time distribution of any bounded initial
hole, restricted to a later compact-containment window, is dominated by
Lebesgue measure. No existence of holes is asserted. -/
theorem ae_cluster_holeExitTime_pushforward_restrict_le_volume_of_steps
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ T : ℝ, t < T →
      closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
      (Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s)))
        ((μ ω).restrict U)).restrict (Ioo t T) ≤ volume := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_mass_singleton_eq_zero hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_holeExitTime_pushforward_interval_le hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_lowerSemicontinuous_clusterHoleExitTime hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω hatom hinterval hlsc hmono
  intro t ht z hz U hU hUb T htT hclT
  let τ := holeExitTime (fun s => closure (cluster (μ ω) 1 z s))
  let ν := Measure.map τ ((μ ω).restrict U)
  have hmeas : Measurable τ := (hlsc z hz).measurable
  have hnull : ∀ c ∈ Ioo t T, ν {c} = 0 := by
    intro c hc
    dsimp [ν]
    rw [Measure.map_apply hmeas (measurableSet_singleton c),
      Measure.restrict_apply (hmeas (measurableSet_singleton c))]
    convert hatom t ht z hz U hU hUb c T hc.1 hc.2 hclT using 1
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    tauto
  let ρ := ν.restrict (Ioo t T)
  have : NullSingletonClass ρ := ⟨fun c => by
    dsimp [ρ]
    rw [Measure.restrict_apply (measurableSet_singleton c)]
    by_cases hc : c ∈ Ioo t T
    · have heq : {c} ∩ Ioo t T = {c} := by
        ext x
        simp only [mem_inter_iff, mem_singleton_iff]
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, hx ▸ hc⟩
      rw [heq, hnull c hc]
    · have heq : {c} ∩ Ioo t T = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        intro hx hxc
        exact hc (hx ▸ hxc)
      rw [heq, measure_empty]⟩
  have hbound : ρ.restrict (Ioo t T) ≤ volume := by
    apply restrict_Ioo_le_volume_of_interval_le ρ
    intro a b hta hab hbT
    have hb : 0 < b := ht.trans_le (hta.trans hab.le)
    have hclb : closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 :=
      (closure_mono (hmono b T 1 hb hbT zero_lt_one z hz)).trans hclT
    exact (Measure.restrict_le_self : ρ ≤ ν) (Ioo a b) |>.trans
      (hinterval t ht z hz U hU hUb a b hta hab hclb)
  simpa only [ρ, Measure.restrict_restrict_of_subset Subset.rfl] using hbound

/-- Under I2 and Lemma 8.2, Lebesgue-null sets of times capture zero
Liouville mass from a bounded initial hole within a compact-containment window.
The time set need not be measurable; the conclusion is simultaneous in it. -/
theorem ae_cluster_holeExitTime_null_preimage_of_steps
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
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
  filter_upwards [ae_cluster_holeExitTime_pushforward_restrict_le_volume_of_steps hI2 h82
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
