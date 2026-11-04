import HarmonicBalls.Proofs.Sec10.HoleCountProcess

/-! # Time-a.e. bounds on the number of holes

Right persistence upgrades a finite count bound from almost every time in an
open interval to every positive time in that interval.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- For a right-persistent extended-natural process, a finite upper bound on
an open time interval follows from its almost-everywhere version. -/
theorem right_persistent_count_bound_iff_null_on_interval (f : ℝ → ℕ∞)
    (hp : ∀ t : ℝ, 0 < t → ∀ n : ℕ, (n : ℕ∞) ≤ f t →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ), (n : ℕ∞) ≤ f s)
    (a b : ℝ) (n : ℕ) :
    (∀ t ∈ Ioo a b, 0 < t → f t ≤ (n : ℕ∞)) ↔
      volume {t : ℝ | t ∈ Ioo a b ∧ 0 < t ∧ (n : ℕ∞) < f t} = 0 := by
  constructor
  · intro h
    have heq : {t : ℝ | t ∈ Ioo a b ∧ 0 < t ∧ (n : ℕ∞) < f t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro t ⟨ht, htpos, htn⟩
      exact (not_lt_of_ge (h t ht htpos)) htn
    rw [heq, measure_empty]
  · intro hnull t ht htpos
    by_contra hle
    have htn : (n : ℕ∞) < f t := lt_of_not_ge hle
    have hnext : ((n + 1 : ℕ) : ℕ∞) ≤ f t := by
      simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr htn
    obtain ⟨δ, hδ, hδp⟩ := hp t htpos (n + 1) hnext
    have hright : t < min b (t + δ) := lt_min ht.2 (lt_add_of_pos_right t hδ)
    have hsub : Ioo t (min b (t + δ)) ⊆
        {s : ℝ | s ∈ Ioo a b ∧ 0 < s ∧ (n : ℕ∞) < f s} := by
      intro s hs
      have hsbound := hδp s ⟨hs.1.le, hs.2.le.trans (min_le_right _ _)⟩
      refine ⟨⟨ht.1.trans hs.1, hs.2.trans_le (min_le_left _ _)⟩,
        htpos.trans hs.1, ?_⟩
      apply ENat.natCast_add_one_le_iff.mp
      simpa only [Nat.cast_add, Nat.cast_one] using hsbound
    have hpositive : 0 < volume (Ioo t (min b (t + δ))) :=
      isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hright)
    exact (ne_of_gt hpositive) (measure_mono_null hsub hnull)

/-- For a right-persistent extended-natural process, a finite upper bound on
an open interval is determined by the positive rational times in it. -/
theorem right_persistent_count_bound_iff_rational_on_interval (f : ℝ → ℕ∞)
    (hp : ∀ t : ℝ, 0 < t → ∀ n : ℕ, (n : ℕ∞) ≤ f t →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ), (n : ℕ∞) ≤ f s)
    (a b : ℝ) (n : ℕ) :
    (∀ t ∈ Ioo a b, 0 < t → f t ≤ (n : ℕ∞)) ↔
      (∀ q : ℚ, (q : ℝ) ∈ Ioo a b → 0 < (q : ℝ) → f q ≤ (n : ℕ∞)) := by
  constructor
  · intro h q hq hqpos
    exact h q hq hqpos
  · intro h t ht htpos
    by_contra hle
    have htn : (n : ℕ∞) < f t := lt_of_not_ge hle
    have hnext : ((n + 1 : ℕ) : ℕ∞) ≤ f t := by
      simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr htn
    obtain ⟨δ, hδ, hδp⟩ := hp t htpos (n + 1) hnext
    have hright : t < min b (t + δ) := lt_min ht.2 (lt_add_of_pos_right t hδ)
    obtain ⟨q, htq, hq⟩ := exists_rat_btwn hright
    have hqbound := hδp q ⟨htq.le, hq.le.trans (min_le_right _ _)⟩
    have hqgt : (n : ℕ∞) < f q := by
      apply ENat.natCast_add_one_le_iff.mp
      simpa only [Nat.cast_add, Nat.cast_one] using hqbound
    exact (not_lt_of_ge (h q ⟨ht.1.trans htq, hq.trans_le (min_le_left _ _)⟩
      (htpos.trans htq))) hqgt

universe u

/-- Under volume growth and the specified Section 6 and 8 inputs, every finite
hole-count bound valid for almost every time in an open interval is valid at
every positive time in that interval, simultaneously for all poles, bounds,
and intervals. -/
theorem ae_cluster_hole_count_bound_iff_time_ae_on_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ a b : ℝ, ∀ n : ℕ,
      (∀ t ∈ Ioo a b, 0 < t → clusterHoleCount (μ ω) z t ≤ (n : ℕ∞)) ↔
      volume {t : ℝ | t ∈ Ioo a b ∧ 0 < t ∧
        (n : ℕ∞) < clusterHoleCount (μ ω) z t} = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_right_persistent hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hp
  intro z hz a b n
  exact right_persistent_count_bound_iff_null_on_interval _ (hp z hz) a b n

/-- A finite bound on the hole count in any open interval is equivalent to
the same bound at its positive rational times, simultaneously for all poles. -/
theorem ae_cluster_hole_count_bound_iff_rational_on_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ a b : ℝ, ∀ n : ℕ,
      (∀ t ∈ Ioo a b, 0 < t → clusterHoleCount (μ ω) z t ≤ (n : ℕ∞)) ↔
      (∀ q : ℚ, (q : ℝ) ∈ Ioo a b → 0 < (q : ℝ) →
        clusterHoleCount (μ ω) z q ≤ (n : ℕ∞)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_right_persistent hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hp
  intro z hz a b n
  exact right_persistent_count_bound_iff_rational_on_interval _ (hp z hz) a b n

end HarmonicBalls
