import HarmonicBalls.Proofs.Sec10.CentreMassStability
import HarmonicBalls.Proofs.Sec10.JointCentreStability
import HarmonicBalls.Proofs.Sec5.InteriorClusterBoundary

/-! # Persistence of holes under motion of the pole

A compact barrier contained in the original cluster can trap a hole of a
nearby cluster, provided some positive mass inside the barrier remains outside
the nearby closed cluster. The existence of such a barrier is not asserted.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped symmDiff

/-- A bounded component of the complement of a barrier traps any component
of the complement of a larger closed set which meets it. -/
theorem bounded_complement_component_of_barrier
    {C K W U : Set ℂ} (hK : K ⊆ closure C)
    (hW : W ∈ connectedComponentsIn Kᶜ) (hWb : Bornology.IsBounded W)
    (hUW : U ⊆ W) (hnot : ¬ U ⊆ closure C) :
    ∃ V ∈ connectedComponentsIn (closure C)ᶜ,
      Bornology.IsBounded V ∧ (V ∩ U).Nonempty := by
  obtain ⟨q, hqU, hqout⟩ := Set.not_subset.mp hnot
  let V := connectedComponentIn (closure C)ᶜ q
  have hV : V ∈ connectedComponentsIn (closure C)ᶜ := ⟨q, hqout, rfl⟩
  have hVW : V ⊆ W := by
    obtain ⟨p, hp, hWp⟩ := hW
    have hqW : q ∈ connectedComponentIn Kᶜ p := hWp.symm ▸ hUW hqU
    have heq : connectedComponentIn Kᶜ q = W :=
      (connectedComponentIn_eq hqW).symm.trans hWp
    exact heq ▸ connectedComponentIn_mono q (compl_subset_compl.mpr hK)
  exact ⟨V, hV, hWb.subset hVW, ⟨q, mem_connectedComponentIn hqout, hqU⟩⟩

universe u

/-- If a compact pole-avoiding barrier traps a positive-mass set outside a
compactly contained cluster, then clusters whose poles converge to the
original pole have bounded complementary components meeting that set
eventually. This is conditional on the existence of the barrier. -/
theorem ae_bounded_hole_persists_of_compact_barrier_under_centre_motion
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z : ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ K W U : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) 1 z t →
      (z : ℂ) ∉ K → W ∈ connectedComponentsIn Kᶜ → Bornology.IsBounded W →
      U ⊆ W → U ⊆ ball 0 1 → U ⊆ (cluster (μ ω) 1 z t)ᶜ → μ ω U ≠ 0 →
      ∀ zs : ℕ → ball (0 : ℂ) 1, Tendsto zs atTop (𝓝 z) →
      ∀ᶠ n in atTop, ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 (zs n) t))ᶜ,
        Bornology.IsBounded V ∧ (V ∩ U).Nonempty := by
  filter_upwards [ae_compact_cluster_measure_continuous_in_centre hI2 h82 hγ hγ2 hα
      P hC hcirc μ hGFF hμ,
    ae_eventually_compact_subset_cluster_of_centre hI2 hγ hγ2 hα P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmass hbarrier hfront hopen
  intro t ht z hcompact K W U hK hKsub hzK hW hWb hUW hUball hUout hUpos zs hzs
  have hlim : Tendsto (fun n => μ ω (U ∩ cluster (μ ω) 1 (zs n) t)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hmass 1 t zero_lt_one ht z hcompact zs hzs)
    · exact Eventually.of_forall fun _ => bot_le
    · apply Eventually.of_forall
      intro n
      apply measure_mono
      intro x hx
      simp only [symmDiff_def]
      exact Or.inr ⟨hx.2, hUout hx.1⟩
  have hsmall := hlim.eventually (Iio_mem_nhds (pos_iff_ne_zero.mpr hUpos))
  have hkeep : ∀ᶠ n in atTop, K ⊆ cluster (μ ω) 1 (zs n) t := by
    have hcoerce : Tendsto (fun n => (zs n : ℂ)) atTop (𝓝 (z : ℂ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hzs
    exact hcoerce.eventually (hbarrier 1 t zero_lt_one ht z z.property K hK hKsub hzK)
  filter_upwards [hsmall, hkeep] with n hn hKn
  apply bounded_complement_component_of_barrier (hKn.trans subset_closure) hW hWb hUW
  intro hcover
  have hsub : U ⊆ (U ∩ cluster (μ ω) 1 (zs n) t) ∪
      (frontier (cluster (μ ω) 1 (zs n) t) ∩ ball 0 1) := by
    intro x hx
    by_cases hxC : x ∈ cluster (μ ω) 1 (zs n) t
    · exact Or.inl ⟨hx, hxC⟩
    · apply Or.inr
      refine ⟨?_, hUball hx⟩
      rw [frontier, (hopen t 1 ht zero_lt_one (zs n) (zs n).property).1.interior_eq]
      exact ⟨hcover hx, hxC⟩
  have hle : μ ω U ≤ μ ω (U ∩ cluster (μ ω) 1 (zs n) t) +
      μ ω (frontier (cluster (μ ω) 1 (zs n) t) ∩ ball 0 1) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [hfront t ht (zs n) (zs n).property, add_zero] at hle
  exact (not_le_of_gt hn) hle

end HarmonicBalls
