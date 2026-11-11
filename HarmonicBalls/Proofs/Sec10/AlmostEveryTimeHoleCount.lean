import HarmonicBalls.Proofs.Sec10.AlmostEveryTimeHolePersistence
import HarmonicBalls.Proofs.Sec10.HoleCountProcess

/-! # Hole counts at almost every deterministic time -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

universe u

/-- Under I2, finite lower bounds on the number of bounded holes persist
on a right interval at almost every deterministic time, almost surely and
simultaneously for any prescribed countable family of poles. -/
theorem ae_time_ae_cluster_hole_count_right_persistent
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {C : Set ℂ} (hcount : C.Countable) (hCsub : C ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t → ∀ z ∈ C, ∀ n : ℕ,
      (n : ℕ∞) ≤ clusterHoleCount (μ ω) z t →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        (n : ℕ∞) ≤ clusterHoleCount (μ ω) z s := by
  classical
  filter_upwards [ae_time_ae_cluster_hole_persistence_for_countable_centres
    hI2 hγ hγ2 hα hGFF hμ hcount hCsub] with t ht
  filter_upwards [ht] with ω hp htpos z hz n hn
  obtain ⟨F, hcard, hF⟩ := (nat_le_encard_iff_exists_finset _ _).mp hn
  have hfinite : ∀ F : Finset (Set ℂ),
      (∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded U) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        ∀ U ∈ F, ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
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
        obtain ⟨δU, hδU, hU⟩ := hp htpos z hz U hU.1 hU.2
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

/-- An almost-sure uniform finite upper bound at positive rational times
also holds almost surely at almost every deterministic time for any given
countable family of poles. -/
theorem ae_time_ae_cluster_hole_count_bound_of_rational_times
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {C : Set ℂ} (hcount : C.Countable) (hCsub : C ⊆ ball (0 : ℂ) 1) (N : ℕ)
    (hrat : ∀ q : ℚ, 0 < (q : ℝ) → ∀ᵐ ω ∂P, ∀ z ∈ C,
      clusterHoleCount (μ ω) z q ≤ N) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t → ∀ z ∈ C,
      clusterHoleCount (μ ω) z t ≤ N := by
  have hratall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → ∀ z ∈ C,
      clusterHoleCount (μ ω) z q ≤ N := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hrat q hq] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_time_ae_cluster_hole_count_right_persistent
    hI2 hγ hγ2 hα hGFF hμ hcount hCsub] with t ht
  filter_upwards [ht, hratall] with ω hp hr htpos z hz
  by_contra hnot
  have hn : ((N + 1 : ℕ) : ℕ∞) ≤ clusterHoleCount (μ ω) z t := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot))
  obtain ⟨δ, hδ, hp⟩ := hp htpos z hz (N + 1) hn
  obtain ⟨q, hqt, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  have hle := (hp q ⟨hqt.le, hq.le⟩).trans (hr q (htpos.trans hqt) z hz)
  exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self N)) hle


end HarmonicBalls
