import HarmonicBalls.Proofs.Sec10.CountableHoleCountExceptions

/-! # Hole-count measurability from volume growth -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- If a set contains a right interval at all but countably many of its
points, it differs from its interior by at most countably many points. -/
theorem countable_sdiff_interior_of_right_intervals_off_countable
    {S E : Set ℝ} (hE : E.Countable)
    (hS : ∀ t ∈ S, t ∉ E → ∃ δ : ℝ, 0 < δ ∧ Ico t (t + δ) ⊆ S) :
    (S \ interior S).Countable := by
  apply (hE.union countable_setOfPred_isolated_right_within).mono
  intro t ht
  by_cases htE : t ∈ E
  · exact Or.inl htE
  · right
    refine ⟨ht, ?_⟩
    obtain ⟨δ, hδ, hinterval⟩ := hS t ht.1 htE
    have hinside : Ioo t (t + δ) ⊆ interior S :=
      interior_maximal (fun _ hx => hinterval ⟨hx.1.le, hx.2⟩) isOpen_Ioo
    rw [← notMem_closure_iff_nhdsWithin_eq_bot]
    intro htcl
    have hnhds : Iio (t + δ) ∈ 𝓝 t := Iio_mem_nhds (lt_add_of_pos_right t hδ)
    obtain ⟨s, hs, hsE⟩ := mem_closure_iff_nhds.mp htcl _ hnhds
    exact hsE.1.2 (hinside ⟨hsE.2, hs⟩)

universe u

/-- Under I2 alone, for every pole and every finite threshold the positive
hole-count level set is Borel and differs from its interior by countably many
times, on one probability-one event. -/
theorem ae_cluster_hole_count_times_measurable_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ n : ℕ,
      let S : Set ℝ := {t | 0 < t ∧ (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t}
      MeasurableSet S ∧ (S \ interior S).Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_times_with_nonpersistent_hole_count hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz n
  dsimp only
  let S : Set ℝ := {t | 0 < t ∧ (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t}
  let E : Set ℝ := {t | 0 < t ∧ ∃ n : ℕ, (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t ∧
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      (n : ℕ∞) ≤ clusterHoleCount (μ ω) z s}
  have hE : E.Countable := hcount z hz
  have hS : ∀ t ∈ S, t ∉ E → ∃ δ : ℝ, 0 < δ ∧ Ico t (t + δ) ⊆ S := by
    intro t ht hnot
    have hp : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        (n : ℕ∞) ≤ clusterHoleCount (μ ω) z s := by
      by_contra hp
      exact hnot ⟨ht.1, n, ht.2, hp⟩
    obtain ⟨δ, hδ, hp⟩ := hp
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    exact ⟨ht.1.trans_le hs.1, hp s ⟨hs.1, hs.2.le⟩⟩
  have hrest := countable_sdiff_interior_of_right_intervals_off_countable hE hS
  have hEq : S = interior S ∪ (S \ interior S) := by
    ext t
    simp only [mem_union, Set.mem_sdiff]
    constructor
    · intro ht
      by_cases h : t ∈ interior S
      · exact Or.inl h
      · exact Or.inr ⟨ht, h⟩
    · rintro (h | h)
      · exact interior_subset h
      · exact h.1
  have hmeas : MeasurableSet S := by
    rw [hEq]
    exact isOpen_interior.measurableSet.union hrest.measurableSet
  exact ⟨hmeas, hrest⟩

/-- The zero-extended bounded-hole count is a Borel function of time under I2,
simultaneously for all poles; infinite counts are allowed. -/
theorem ae_cluster_hole_count_measurable_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      Measurable (fun t : ℝ => if 0 < t then clusterHoleCount (μ ω) z t else 0) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_times_measurable_of_volumeGrowth hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlevel
  intro z hz
  apply measurable_zero_extend_of_nat_upper_levels
  exact fun n => (hlevel z hz n).1

#print axioms ae_cluster_hole_count_times_measurable_of_volumeGrowth
#print axioms ae_cluster_hole_count_measurable_of_volumeGrowth

end HarmonicBalls
