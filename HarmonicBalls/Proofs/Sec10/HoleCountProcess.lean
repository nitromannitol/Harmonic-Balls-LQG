import HarmonicBalls.Proofs.Sec10.HoleCountTimeMeasurability

/-! # The bounded-hole count as a measurable process

The extended natural count allows infinitely many complementary holes. The
measurability asserted here is pathwise in time, simultaneously in the pole.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- The number of bounded complementary components of a cluster closure. -/
noncomputable def clusterHoleCount (μ : Measure ℂ) (z : ℂ) (t : ℝ) : ℕ∞ :=
  {U : Set ℂ | U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ ∧
    Bornology.IsBounded U}.encard

/-- An extended cardinal reaches a finite threshold exactly when a finite
subset reaches that threshold. -/
theorem nat_le_encard_iff_exists_finset {α : Type*} (S : Set α) (n : ℕ) :
    (n : ℕ∞) ≤ S.encard ↔ ∃ F : Finset α, n ≤ F.card ∧ ∀ a ∈ F, a ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_encard_eq h
    have hTf : T.Finite := Set.finite_of_encard_eq_coe hTcard
    refine ⟨hTf.toFinset, ?_, ?_⟩
    · have heq : hTf.toFinset.card = n := by
        have hcast : (hTf.toFinset.card : ℕ∞) = (n : ℕ∞) := by
          simpa only [hTf.encard_eq_coe_toFinset_card] using hTcard
        exact_mod_cast hcast
      exact heq.ge
    · intro a ha
      exact hTS (hTf.mem_toFinset.mp ha)
  · rintro ⟨F, hF, hFS⟩
    have hsub : (F : Set α) ⊆ S := by
      intro a ha
      exact hFS a ha
    have hcard := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at hcard
    exact (ENat.natCast_le_natCast.mpr hF).trans hcard

/-- A positive-time process into the extended naturals is measurable if all
its finite upper-level sets are measurable. The value at nonpositive times is
set to zero. -/
theorem measurable_zero_extend_of_nat_upper_levels (f : ℝ → ℕ∞)
    (h : ∀ n : ℕ, MeasurableSet {t | 0 < t ∧ (n : ℕ∞) ≤ f t}) :
    Measurable (fun t : ℝ => if 0 < t then f t else 0) := by
  classical
  apply ENat.measurable_iff.mpr
  intro n
  have heq : (fun t : ℝ => if 0 < t then f t else 0) ⁻¹' {(n : ℕ∞)} =
      ({t | 0 < t ∧ (n : ℕ∞) ≤ f t} \ {t | 0 < t ∧ ((n + 1 : ℕ) : ℕ∞) ≤ f t}) ∪
        (if n = 0 then Iic 0 else ∅) := by
    ext t
    by_cases ht : 0 < t
    · have ht' : ¬ t ≤ 0 := not_le_of_gt ht
      simp only [mem_preimage, mem_singleton_iff, mem_union, Set.mem_sdiff, mem_ofPred_eq,
        mem_Iic, mem_ite_empty_right, ht, ite_true, true_and, ht', and_false, or_false,
        not_le, Nat.cast_add, Nat.cast_one, ENat.lt_natCast_add_one_iff]
      exact ⟨fun he => ⟨he.ge, he.le⟩, fun hh => le_antisymm hh.2 hh.1⟩
    · have ht' : t ≤ 0 := le_of_not_gt ht
      simp [ht, ht', eq_comm]
  rw [heq]
  exact ((h n).diff (h (n + 1))).union (by split <;> simp [measurableSet_Iic])

universe u

/-- Under volume growth and the specified Section 6 and 8 inputs, the count of
bounded cluster holes, zero-extended to nonpositive times, is measurable in
time simultaneously for every pole. Infinite counts are allowed. -/
theorem ae_cluster_hole_count_measurable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      Measurable (fun t : ℝ => if 0 < t then clusterHoleCount (μ ω) z t else 0) := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_times_measurable hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz
  apply measurable_zero_extend_of_nat_upper_levels
  intro n
  convert (hcount z hz n).1 using 1
  ext t
  simp only [mem_ofPred_eq, clusterHoleCount, nat_le_encard_iff_exists_finset]

/-- Every finite lower bound on the hole count persists for a positive right
interval, even when the initial cluster touches the unit circle. The interval
may depend on the threshold. -/
theorem ae_cluster_hole_count_right_persistent
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ n : ℕ,
      (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        (n : ℕ∞) ≤ clusterHoleCount (μ ω) z s := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_finite_cluster_holes_inject_at_boundary_contact hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz t ht n hn
  obtain ⟨F, hcard, hF⟩ := (nat_le_encard_iff_exists_finset _ _).mp hn
  obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz F hF
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hVinj, hV⟩ := hp s hs
  apply (nat_le_encard_iff_exists_finset _ _).mpr
  refine ⟨F.attach.image V, ?_, ?_⟩
  · simpa [Finset.card_image_of_injective _ hVinj] using hcard
  · intro U hU
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨(hV W).1, (hV W).2.1⟩

/-- The positive times at which the cluster has infinitely many bounded holes
form a Borel set, simultaneously for every pole. -/
theorem ae_infinite_cluster_hole_times_measurable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      MeasurableSet {t : ℝ | 0 < t ∧ clusterHoleCount (μ ω) z t = ⊤} := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_measurable hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz
  have h := (hcount z hz) (measurableSet_singleton (⊤ : ℕ∞))
  have heq : (fun t : ℝ => if 0 < t then clusterHoleCount (μ ω) z t else 0) ⁻¹'
      {(⊤ : ℕ∞)} = {t : ℝ | 0 < t ∧ clusterHoleCount (μ ω) z t = ⊤} := by
    ext t
    by_cases ht : 0 < t <;> simp [ht]
  rwa [heq] at h

end HarmonicBalls
