import HarmonicBalls.Proofs.Sec10.FiniteHoleCounts
import Mathlib.Topology.Order.LeftRightNhds

/-! # Measurability of hole-count times

A set of real times which persists for a right interval differs from its
interior by at most countably many times. Finite-hole persistence gives this
regularity for every hole-count threshold.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- A set which contains a right interval at each of its points differs from
its interior by a countable set. -/
theorem countable_sdiff_interior_of_right_intervals {S : Set ℝ}
    (hS : ∀ t ∈ S, ∃ δ : ℝ, 0 < δ ∧ Ico t (t + δ) ⊆ S) :
    (S \ interior S).Countable := by
  apply countable_setOfPred_isolated_right_within.mono
  intro t ht
  refine ⟨ht, ?_⟩
  obtain ⟨δ, hδ, hinterval⟩ := hS t ht.1
  have hinside : Ioo t (t + δ) ⊆ interior S :=
    interior_maximal (fun _ hx => hinterval ⟨hx.1.le, hx.2⟩) isOpen_Ioo
  rw [← notMem_closure_iff_nhdsWithin_eq_bot]
  intro htcl
  have hnhds : Iio (t + δ) ∈ 𝓝 t := Iio_mem_nhds (lt_add_of_pos_right t hδ)
  obtain ⟨s, hs, hsE⟩ := mem_closure_iff_nhds.mp htcl _ hnhds
  exact hsE.1.2 (hinside ⟨hsE.2, hs⟩)

/-- A right-persistent set of times is Borel measurable. -/
theorem measurableSet_of_right_intervals {S : Set ℝ}
    (hS : ∀ t ∈ S, ∃ δ : ℝ, 0 < δ ∧ Ico t (t + δ) ⊆ S) :
    MeasurableSet S := by
  have heq : S = interior S ∪ (S \ interior S) := by
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
  rw [heq]
  exact isOpen_interior.measurableSet.union (countable_sdiff_interior_of_right_intervals hS).measurableSet

universe u

/-- Under volume growth and the stated Section 6 and 8 inputs, the times at
which there are at least `n` bounded holes form a Borel set, differing from an
open set by at most countably many times. This holds simultaneously for all
poles and thresholds, including at unit-boundary contact. -/
theorem ae_cluster_hole_count_times_measurable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ n : ℕ,
      let S : Set ℝ := {t | 0 < t ∧ ∃ F : Finset (Set ℂ), n ≤ F.card ∧
        ∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U}
      MeasurableSet S ∧ (S \ interior S).Countable := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_finite_cluster_holes_inject_at_boundary_contact hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hpersist
  intro z hz n
  dsimp only
  let S : Set ℝ := {t | 0 < t ∧ ∃ F : Finset (Set ℂ), n ≤ F.card ∧
    ∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
      Bornology.IsBounded U}
  have hS : ∀ t ∈ S, ∃ δ : ℝ, 0 < δ ∧ Ico t (t + δ) ⊆ S := by
    intro t htS
    rcases htS with ⟨ht, F, hcard, hF⟩
    obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz F hF
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    obtain ⟨V, hVinj, hV⟩ := hp s ⟨hs.1, hs.2.le⟩
    refine ⟨ht.trans_le hs.1, F.attach.image V, ?_, ?_⟩
    · simpa [Finset.card_image_of_injective _ hVinj] using hcard
    · intro U hU
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
      exact ⟨(hV W).1, (hV W).2.1⟩
  exact ⟨measurableSet_of_right_intervals hS, countable_sdiff_interior_of_right_intervals hS⟩

/-- The set of positive times with at least one bounded complementary hole is
Borel and differs from its interior by a countable set. -/
theorem ae_cluster_hole_times_measurable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      let S : Set ℝ := {t | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U}
      MeasurableSet S ∧ (S \ interior S).Countable := by
  classical
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_count_times_measurable hI2 h611 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz
  have heq : {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
      (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U} =
      {t : ℝ | 0 < t ∧ ∃ F : Finset (Set ℂ), 1 ≤ F.card ∧
        ∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U} := by
    ext t
    constructor
    · rintro ⟨ht, U, hU, hb⟩
      refine ⟨ht, {U}, by simp, ?_⟩
      simpa only [Finset.mem_singleton, forall_eq] using And.intro hU hb
    · rintro ⟨ht, F, hcard, hF⟩
      obtain ⟨U, hU⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
      exact ⟨ht, U, (hF U hU).1, (hF U hU).2⟩
  simpa only [heq] using hcount z hz 1

end HarmonicBalls
