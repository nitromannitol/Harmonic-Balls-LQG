import HarmonicBalls.Proofs.Sec10.HoleExtinctionCoverage
import HarmonicBalls.Proofs.Sec10.HolePersistenceAtBoundaryContact

/-! # Hole extinction at the lifetime endpoint

Right persistence excludes descendants at the lifetime endpoint even when
that cluster touches the unit circle. Interior frontier nullity then gives
almost-everywhere coverage of the original hole before extinction.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- A bounded hole of a compactly contained cluster has no descendant at its
finite lifetime endpoint, and almost all of the hole is swallowed strictly
before that endpoint. The endpoint need not be compactly contained. -/
theorem ae_cluster_hole_extinction_at_lifetime_endpoint
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
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
        (∀ s : ℝ, L ≤ s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        U ⊆ closure (cluster (μ ω) 1 z L) ∧
        μ ω (U \ ⋃ s ∈ Ico t L, cluster (μ ω) 1 z s) = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_bounded_hole_has_finite_lifetime hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_hole_persists_at_boundary_contact hI2 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2) h611 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlife hpersist hmono hopen hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter⟩ := hlife t ht z hz hcl U hU hUb
  have hLpos := ht.trans htL
  have hnoL : ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z L))ᶜ,
      V ⊆ U := by
    rintro ⟨V, hV, hVU⟩
    have hVb : Bornology.IsBounded V := hUb.subset hVU
    obtain ⟨δ, hδ, hp⟩ := hpersist L hLpos z hz V hV hVb
    have hLs : L < L + δ / 2 := lt_add_of_pos_right L (half_pos hδ)
    have hs : L + δ / 2 ∈ Icc L (L + δ) := by constructor <;> linarith
    obtain ⟨W, hW, _, hWV⟩ := hp (L + δ / 2) hs
    exact hafter (L + δ / 2) hLs ⟨W, hW, hWV.trans hVU⟩
  have hno : ∀ s : ℝ, L ≤ s →
      ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        V ⊆ U := by
    intro s hLs
    rcases hLs.eq_or_lt with rfl | hLs
    · exact hnoL
    · exact hafter s hLs
  have hcover : U ⊆ closure (cluster (μ ω) 1 z L) :=
    complement_component_subset_of_no_descendant
      (closure_mono (hmono t L 1 ht htL.le zero_lt_one z hz)) hU hnoL
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (hcl.trans ball_subset_closedBall) hU hUb
  have hUout : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    obtain ⟨x, hx, rfl⟩ := hU
    exact connectedComponentIn_subset _ _
  refine ⟨L, htL, hbefore, hno, hcover, ?_⟩
  apply measure_mono_null _ (hnull L hLpos z hz)
  intro x hx
  have hxnot : x ∉ cluster (μ ω) 1 z L := by
    intro hxL
    obtain ⟨q, hqpos, hqL, hxq⟩ := mem_cluster_exists_earlier_rat hLpos hxL
    have htq : t ≤ (q : ℝ) := by
      by_contra h
      have hqt : (q : ℝ) ≤ t := (lt_of_not_ge h).le
      exact hUout hx.1 (subset_closure (hmono q t 1 hqpos hqt zero_lt_one z hz hxq))
    exact hx.2 (mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨⟨htq, hqL⟩, hxq⟩⟩)
  refine ⟨?_, hUdisc hx.1⟩
  rw [(hopen L 1 hLpos zero_lt_one z hz).1.frontier_eq]
  exact ⟨hcover hx.1, hxnot⟩

end HarmonicBalls
