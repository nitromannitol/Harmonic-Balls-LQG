import HarmonicBalls.Proofs.Sec5.AlmostEveryTimeContinuity
import HarmonicBalls.Proofs.Sec10.GenericTimeHolePersistence

/-! # Hole persistence at almost every deterministic time -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

universe u

/-- Under I2, every bounded complementary component persists on a right
interval at almost every deterministic time, almost surely and simultaneously
for any prescribed countable family of poles. -/
theorem ae_time_ae_cluster_hole_persistence_for_countable_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {C : Set ℂ} (hcount : C.Countable) (hCsub : C ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t → ∀ z ∈ C,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U := by
  filter_upwards [ae_time_ae_lqg_cluster_right_continuous_for_countable_centres
    hI2 hγ hγ2 hα hGFF hμ hcount hCsub] with t htime
  filter_upwards [htime, clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hcont hmono ht z hz U hU hbounded
  obtain ⟨δ, hδ, hp⟩ := complement_component_persists_of_right_continuity
    (fun s hts => hmono t s 1 ht hts zero_lt_one z (hCsub hz)) (hcont z hz ht) hU
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hV, hVU⟩ := hp s hs
  exact ⟨V, hV, hbounded.subset hVU, hVU⟩

/-- If each positive rational time has no holes almost surely for the given
countable family of poles, then almost every deterministic time has no holes
almost surely for that family. -/
theorem ae_time_ae_no_holes_of_rational_times_for_countable_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {C : Set ℂ} (hcount : C.Countable) (hCsub : C ⊆ ball (0 : ℂ) 1)
    (hrat : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P, ∀ z ∈ C,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z q))ᶜ,
        ¬ Bornology.IsBounded U) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t → ∀ z ∈ C,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ Bornology.IsBounded U := by
  have hratall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → ∀ z ∈ C,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z q))ᶜ,
        ¬ Bornology.IsBounded U := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hrat q hq] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_time_ae_cluster_hole_persistence_for_countable_centres
    hI2 hγ hγ2 hα hGFF hμ hcount hCsub] with t ht
  filter_upwards [ht, hratall] with ω hp hr htpos z hz U hU hb
  obtain ⟨δ, hδ, hp⟩ := hp htpos z hz U hU hb
  obtain ⟨q, hqt, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  obtain ⟨V, hV, hbV, _⟩ := hp q ⟨hqt.le, hq.le⟩
  exact hr q (htpos.trans hqt) z hz V hV hbV


end HarmonicBalls
