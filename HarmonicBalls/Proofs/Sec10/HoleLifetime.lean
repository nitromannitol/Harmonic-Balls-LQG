import HarmonicBalls.Proofs.Sec10.LateTimeHoles
import HarmonicBalls.Proofs.Sec10.SimultaneousHolePersistence
import HarmonicBalls.Proofs.Sec5.DiscClusterExhaustion

/-! # Lifetime of a bounded complementary component

A bounded hole present while the cluster is compactly contained has a
positive, finite interval of descendant times. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- A bounded complementary component inside a smaller open disc has compact
closure inside that disc. -/
theorem bounded_complement_component_closure_subset_unit_ball
    {K U : Set ℂ} (hKclosed : IsClosed K) (hK : K ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn Kᶜ) (hUb : Bornology.IsBounded U) :
    IsCompact (closure U) ∧ closure U ⊆ ball (0 : ℂ) 1 := by
  refine ⟨hUb.isCompact_closure, ?_⟩
  have hUsub := bounded_complement_component_subset_unit_ball hKclosed
    (hK.trans ball_subset_closedBall) hU hUb
  obtain ⟨p, hp, hpU⟩ := hU
  have hopen : IsOpen U := by
    rw [← hpU]
    exact hKclosed.isOpen_compl.connectedComponentIn
  have hfront : frontier U ⊆ K := by
    rw [← hpU]
    have h := frontier_connectedComponentIn_subset_frontier hKclosed.isOpen_compl p
    rw [frontier_compl] at h
    exact h.trans (by simpa only [hKclosed.closure_eq] using
      (frontier_subset_closure : frontier K ⊆ closure K))
  intro x hx
  by_cases hxU : x ∈ U
  · exact hUsub hxU
  · apply hK
    apply hfront
    rw [frontier, hopen.interior_eq]
    exact ⟨hx, hxU⟩

/-- If an increasing family of closed sets has a complementary component
inside `U` at a later time, one such component exists at every intermediate
time, provided `U` is an earlier complementary component. -/
theorem component_descendant_at_intermediate_time
    {F : ℝ → Set ℂ} {t r s : ℝ} {U V : Set ℂ}
    (htr : t ≤ r) (hrs : r ≤ s)
    (hmono : ∀ a b, t ≤ a → a ≤ b → F a ⊆ F b)
    (hU : U ∈ connectedComponentsIn (F t)ᶜ)
    (hV : V ∈ connectedComponentsIn (F s)ᶜ) (hVU : V ⊆ U) :
    ∃ W ∈ connectedComponentsIn (F r)ᶜ, W ⊆ U := by
  obtain ⟨x, hx, hxV⟩ := hV
  have hxV' : x ∈ V := hxV ▸ mem_connectedComponentIn hx
  have hxU : x ∈ U := hVU hxV'
  have hxs : x ∈ (F s)ᶜ := hx
  have hxr : x ∈ (F r)ᶜ := (compl_subset_compl.mpr (hmono r s htr hrs)) hxs
  let W := connectedComponentIn (F r)ᶜ x
  refine ⟨W, ⟨x, hxr, rfl⟩, ?_⟩
  obtain ⟨y, hy, hyU⟩ := hU
  have hWsub : W ⊆ (F t)ᶜ :=
    (connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr (hmono t r le_rfl htr))
  have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWx : x ∈ W := mem_connectedComponentIn hxr
  have h := hWpre.subset_connectedComponentIn hWx hWsub
  have hxUy : x ∈ connectedComponentIn (F t)ᶜ y := hyU.symm ▸ hxU
  have heq : connectedComponentIn (F t)ᶜ x = U := (connectedComponentIn_eq hxUy).symm.trans hyU
  exact heq ▸ h

universe u

/-- Every bounded hole of a compactly contained cluster has a strictly
positive, finite descendant lifetime. Descendants exist throughout the
half-open interval below the lifetime and do not exist after it; behavior
at the endpoint is not asserted. -/
theorem ae_cluster_bounded_hole_has_finite_lifetime
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, L < s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    ae_cluster_hole_persists_on_right_interval hI2 h82 γ hγ hγ2 α₀ hα
      Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hpersist hmono
  intro t ht z hz hcl U hU hUb
  obtain ⟨hUc, hUdisc⟩ := bounded_complement_component_closure_subset_unit_ball
    isClosed_closure hcl hU hUb
  obtain ⟨T, hT, hentry⟩ := exists_cluster_contains_compact_of_volumeGrowth
    hV.1 zero_lt_one (hV.2 1 zero_lt_one) hz hUc hUdisc
  obtain ⟨δ, hδ, hp⟩ := hpersist t ht z hz hcl U hU hUb
  let S : Set ℝ := {s | t ≤ s ∧
    ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U}
  have hSnon : S.Nonempty := ⟨t, le_rfl, U, hU, Subset.rfl⟩
  have hno (s : ℝ) (hs : T ≤ s) :
      ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U := by
    rintro ⟨V, ⟨x, hx, hxV⟩, hVU⟩
    have hxU : x ∈ U := hVU (hxV ▸ mem_connectedComponentIn hx)
    exact hx (subset_closure (hentry s hs (subset_closure hxU)))
  have hSbd : BddAbove S := by
    refine ⟨T, ?_⟩
    intro s hs
    exact le_of_not_gt (fun hTs => hno s hTs.le hs.2)
  have hsmall : t + δ / 2 ∈ S := by
    have ht' : t ≤ t + δ / 2 := le_add_of_nonneg_right (half_pos hδ).le
    have hlt : t + δ / 2 < t + δ := add_lt_add_of_le_of_lt le_rfl (half_lt_self hδ)
    obtain ⟨V, hV, _, hVU⟩ := hp (t + δ / 2) ht' hlt
    exact ⟨ht', V, hV, hVU⟩
  refine ⟨sSup S, (lt_add_of_pos_right t (half_pos hδ)).trans_le (le_csSup hSbd hsmall), ?_, ?_⟩
  · intro s hts hsL
    obtain ⟨v, hv, hsv⟩ := exists_lt_of_lt_csSup hSnon hsL
    obtain ⟨V, hV, hVU⟩ := hv.2
    apply component_descendant_at_intermediate_time hts hsv.le ?_ hU hV hVU
    intro a b hta hab
    exact closure_mono (hmono a b 1 (ht.trans_le hta) hab zero_lt_one z hz)
  · intro s hsL hdesc
    have hts : t ≤ s := le_of_lt ((lt_of_lt_of_le
      (lt_add_of_pos_right t (half_pos hδ)) (le_csSup hSbd hsmall)).trans hsL)
    exact (not_le_of_gt hsL) (le_csSup hSbd ⟨hts, hdesc⟩)

end HarmonicBalls
