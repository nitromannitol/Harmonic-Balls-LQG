import HarmonicBalls.Proofs.Sec10.CountableHoleCountExceptions

/-! # Hole-count bounds outside countably many times -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under I2, a finite upper bound on the number of bounded holes at a dense
set of times can fail at only countably many positive times. The exceptional
set may depend on the pole and on the bound. -/
theorem ae_countable_hole_count_bound_exceptions_of_dense_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (T : Set ℝ) (hT : Dense T) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ N : ℕ,
      (∀ t ∈ T, 0 < t → clusterHoleCount (μ ω) z t ≤ N) →
      {t : ℝ | 0 < t ∧ ¬ clusterHoleCount (μ ω) z t ≤ N}.Countable := by
  filter_upwards [ae_countable_times_with_nonpersistent_hole_count hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz N hbound
  apply (hcount z hz).mono
  rintro t ⟨ht, hnot⟩
  have hn : ((N + 1 : ℕ) : ℕ∞) ≤ clusterHoleCount (μ ω) z t := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot))
  refine ⟨ht, N + 1, hn, ?_⟩
  rintro ⟨δ, hδ, hp⟩
  obtain ⟨s, hs, hsT⟩ := hT.inter_open_nonempty (Ioo t (t + δ))
    isOpen_Ioo (nonempty_Ioo.mpr (lt_add_of_pos_right t hδ))
  have hle := (hp s ⟨hs.1.le, hs.2.le⟩).trans (hbound s hsT (ht.trans hs.1))
  exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self N)) hle

/-- If the same finite bound holds almost surely for all poles in `Z` at
almost every deterministic time, then almost surely it holds outside a
countable set of times for each pole in `Z`. -/
theorem ae_countable_hole_count_bound_exceptions_of_ae_deterministic_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Z : Set ℂ) (hZ : Z ⊆ ball (0 : ℂ) 1) (N : ℕ)
    (htime : ∀ᵐ t ∂(volume : Measure ℝ), 0 < t →
      ∀ᵐ ω ∂P, ∀ z ∈ Z, clusterHoleCount (μ ω) z t ≤ N) :
    ∀ᵐ ω ∂P, ∀ z ∈ Z,
      {t : ℝ | 0 < t ∧ ¬ clusterHoleCount (μ ω) z t ≤ N}.Countable := by
  classical
  let S : Set ℝ := {t | 0 < t → ∀ᵐ ω ∂P, ∀ z ∈ Z,
    clusterHoleCount (μ ω) z t ≤ N}
  have hS : Dense S := Measure.dense_of_ae htime
  obtain ⟨T, hTS, hcount, hdense⟩ := hS.exists_countable_dense_subset
  let : Countable T := hcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ t : T, 0 < (t : ℝ) → ∀ z ∈ Z,
      clusterHoleCount (μ ω) z t ≤ N := by
    apply ae_all_iff.mpr
    intro t
    by_cases ht : 0 < (t : ℝ)
    · filter_upwards [(hTS t.property) ht] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => (ht h).elim
  filter_upwards [hall, ae_countable_hole_count_bound_exceptions_of_dense_times
    hI2 hγ hγ2 hα P hC hcirc μ hGFF hμ T hdense] with ω hω hexcept
  intro z hz
  apply hexcept z (hZ hz) N
  intro t htT ht
  exact hω ⟨t, htT⟩ ht z hz

#print axioms ae_countable_hole_count_bound_exceptions_of_dense_times
#print axioms ae_countable_hole_count_bound_exceptions_of_ae_deterministic_time

end HarmonicBalls
