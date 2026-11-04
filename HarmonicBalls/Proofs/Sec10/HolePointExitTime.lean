import HarmonicBalls.Proofs.Sec10.HoleCompactPersistence
import HarmonicBalls.Proofs.Sec10.HolePointTimeInterval

/-! # Pointwise exit from holes

A point already in a bounded complementary component remains in a hole until
a finite exit time. Interior right continuity places the exit point on the
cluster frontier and excludes the exit time itself from the hole-time interval.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under interior cluster continuity, every point in a bounded hole has a
finite later exit time, belongs to a hole at all intermediate times, and lies
on the cluster frontier at the exit time. No hole existence is asserted. -/
theorem ae_cluster_hole_point_exit_on_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, ∀ x : ℂ,
      x ∈ (closure (cluster (μ ω) 1 z t))ᶜ →
      Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x) →
      ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          x ∈ (closure (cluster (μ ω) 1 z s))ᶜ ∧
          Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x)) ∧
        x ∈ frontier (cluster (μ ω) 1 z L) ∧
        (∀ s : ℝ, L ≤ s → x ∈ closure (cluster (μ ω) 1 z s)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_bddAbove_ordConnected hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_hole_closedBall_persists hI2 hvolume h61 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω htimes hpersist hmono hopen
  intro t ht z hz x hx hb
  let S : Set ℝ := {s | 0 < s ∧ x ∈ (closure (cluster (μ ω) 1 z s))ᶜ ∧
    Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x)}
  let L := sSup S
  have htS : t ∈ S := ⟨ht, hx, hb⟩
  have hSord : S.OrdConnected := (htimes z hz x).1
  have hSb : BddAbove S := (htimes z hz x).2
  have hLnot : L ∉ S := by
    intro hLS
    have hU : connectedComponentIn (closure (cluster (μ ω) 1 z L))ᶜ x ∈
        connectedComponentsIn (closure (cluster (μ ω) 1 z L))ᶜ := ⟨x, hLS.2.1, rfl⟩
    have hxU := mem_connectedComponentIn hLS.2.1
    obtain ⟨r, δ, hr, hδ, hdesc⟩ := hpersist L hLS.1 z hz _ hU hLS.2.2 x hxU
    have hLs : L < L + δ / 2 := lt_add_of_pos_right L (half_pos hδ)
    have hsint : L + δ / 2 ∈ Icc L (L + δ) := by constructor <;> linarith
    obtain ⟨V, hV, hVb, hball, hVU⟩ := hdesc (L + δ / 2) hsint
    have hxV : x ∈ V := hball (mem_closedBall_self hr.le)
    have hxout : x ∈ (closure (cluster (μ ω) 1 z (L + δ / 2)))ᶜ := by
      obtain ⟨y, hy, rfl⟩ := hV
      exact connectedComponentIn_subset _ _ hxV
    have hbounded := (bounded_complement_component_mono_at_point
      (closure_mono (hmono L (L + δ / 2) 1 hLS.1 hLs.le zero_lt_one z hz))
      hxout hLS.2.2).2.2
    have hsS : L + δ / 2 ∈ S := ⟨hLS.1.trans hLs, hxout, hbounded⟩
    exact (not_lt_of_ge (le_csSup hSb hsS)) hLs
  have htL : t < L := lt_of_le_of_ne (le_csSup hSb htS) (fun heq => hLnot (heq ▸ htS))
  have hLpos : 0 < L := ht.trans htL
  have hbetween : ∀ s : ℝ, t ≤ s → s < L → s ∈ S := by
    intro s hts hsL
    obtain ⟨r, hrS, hsr⟩ := exists_lt_of_lt_csSup ⟨t, htS⟩ hsL
    exact hSord.out htS hrS ⟨hts, hsr.le⟩
  have hxL : x ∈ closure (cluster (μ ω) 1 z L) := by
    by_contra hxnot
    have hxout : x ∈ (closure (cluster (μ ω) 1 z L))ᶜ := hxnot
    have hbound := (bounded_complement_component_mono_at_point
      (closure_mono (hmono t L 1 ht htL.le zero_lt_one z hz)) hxout hb).2.2
    exact hLnot ⟨hLpos, hxout, hbound⟩
  have hxnotL : x ∉ cluster (μ ω) 1 z L := by
    intro hxC
    obtain ⟨q, hq0, hqL, hxq⟩ := mem_cluster_exists_earlier_rat hLpos hxC
    obtain ⟨s, hsS, hqs⟩ := exists_lt_of_lt_csSup ⟨t, htS⟩ hqL
    have hxs : x ∈ cluster (μ ω) 1 z s := hmono q s 1 hq0 hqs.le zero_lt_one z hz hxq
    exact hsS.2.1 (subset_closure hxs)
  refine ⟨L, htL, ?_, ?_, ?_⟩
  · intro s hts hsL
    exact (hbetween s hts hsL).2
  · rw [(hopen L 1 hLpos zero_lt_one z hz).1.frontier_eq]
    exact ⟨hxL, hxnotL⟩
  · intro s hLs
    exact closure_mono (hmono L s 1 hLpos hLs zero_lt_one z hz) hxL

end HarmonicBalls
