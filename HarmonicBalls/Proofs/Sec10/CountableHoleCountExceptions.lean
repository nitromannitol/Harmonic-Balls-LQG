import HarmonicBalls.Proofs.Sec10.AlmostEveryTimeHoleCount
import HarmonicBalls.Proofs.Sec10.GenericTimeHolePersistence

/-! # Countable exceptions for hole-count persistence -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

universe u

/-- If each bounded complementary component has a later descendant in a
right interval, then every finite lower bound on the count persists. -/
theorem cluster_hole_count_right_persistent_of_component_persistence
    {μ : Measure ℂ} {z : ℂ} {t : ℝ}
    (hp : ∀ U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∃ V ∈ connectedComponentsIn (closure (cluster μ 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U)
    {n : ℕ} (hn : (n : ℕ∞) ≤ clusterHoleCount μ z t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      (n : ℕ∞) ≤ clusterHoleCount μ z s := by
  classical
  obtain ⟨F, hcard, hF⟩ := (nat_le_encard_iff_exists_finset _ _).mp hn
  have hfinite : ∀ F : Finset (Set ℂ),
      (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ ∧
        Bornology.IsBounded U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∀ U ∈ F, ∃ V ∈ connectedComponentsIn (closure (cluster μ 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨1, zero_lt_one, ?_⟩
        simp
    | @insert U F hUF ih =>
        intro hF
        have hU := hF U (Finset.mem_insert_self U F)
        obtain ⟨δU, hδU, hU⟩ := hp U hU.1 hU.2
        obtain ⟨δF, hδF, hF⟩ := ih (by
          intro V hV
          exact hF V (Finset.mem_insert_of_mem hV))
        refine ⟨min δU δF, lt_min hδU hδF, ?_⟩
        intro s hs V hV
        rcases Finset.mem_insert.mp hV with rfl | hV
        · exact hU s ⟨hs.1, hs.2.trans (add_le_add le_rfl (min_le_left _ _))⟩
        · exact hF s ⟨hs.1, hs.2.trans (add_le_add le_rfl (min_le_right _ _))⟩ V hV
  obtain ⟨δ, hδ, hδF⟩ := hfinite F hF
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  choose V hV using fun U : {U // U ∈ F} => hδF s hs U.1 U.2
  have hVinj : Function.Injective V := by
    intro U W heq
    apply Subtype.ext
    by_contra hne
    obtain ⟨x, hx, hxV⟩ := (hV U).1
    have hxU : x ∈ U.1 := (hV U).2.2 (hxV ▸ mem_connectedComponentIn hx)
    have hxW : x ∈ W.1 := (hV W).2.2 (heq ▸ hxV ▸ mem_connectedComponentIn hx)
    exact (disjoint_left.mp (connectedComponentsIn_pairwise_disjoint _
      (hF U.1 U.2).1 (hF W.1 W.2).1 hne)) hxU hxW
  apply (nat_le_encard_iff_exists_finset _ _).mpr
  refine ⟨F.attach.image V, ?_, ?_⟩
  · simpa [Finset.card_image_of_injective _ hVinj] using hcard
  · intro U hU
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨(hV W).1, (hV W).2.1⟩

/-- Under I2, almost surely for every pole, all finite lower bounds on the
hole count persist to the right outside a countable set of positive times.
The exceptional set can depend on the pole. -/
theorem ae_countable_times_with_nonpersistent_hole_count
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ∃ n : ℕ, (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t ∧
        ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          (n : ℕ∞) ≤ clusterHoleCount (μ ω) z s}.Countable := by
  classical
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_times_with_nonpersistent_component hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz
  apply (hcount z hz).mono
  rintro t ⟨ht, n, hn, hnot⟩
  by_contra hbad
  apply hnot
  apply cluster_hole_count_right_persistent_of_component_persistence _ hn
  intro U hU hUb
  by_contra hUbad
  apply hbad
  refine ⟨ht, U, hU, ?_⟩
  intro hp
  apply hUbad
  obtain ⟨δ, hδ, hp⟩ := hp
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨V, hV, hVU⟩ := hp s hs
  exact ⟨V, hV, hUb.subset hVU, hVU⟩

/-- A finite upper bound at all positive rational times fails at at most
countably many positive real times, simultaneously for every pole. -/
theorem ae_countable_hole_count_bound_exceptions_of_rational_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ N : ℕ,
      (∀ q : ℚ, 0 < (q : ℝ) → clusterHoleCount (μ ω) z q ≤ N) →
      {t : ℝ | 0 < t ∧ ¬ clusterHoleCount (μ ω) z t ≤ N}.Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_times_with_nonpersistent_hole_count hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz N hrat
  apply (hcount z hz).mono
  rintro t ⟨ht, hnot⟩
  have hn : ((N + 1 : ℕ) : ℕ∞) ≤ clusterHoleCount (μ ω) z t := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot))
  refine ⟨ht, N + 1, hn, ?_⟩
  rintro ⟨δ, hδ, hp⟩
  obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  have hle := (hp q ⟨htq.le, hq.le⟩).trans (hrat q (ht.trans htq))
  exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self N)) hle


end HarmonicBalls
