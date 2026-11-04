import HarmonicBalls.Proofs.Sec10.HoleLifetime

/-! # Hole persistence and mass at the lifetime endpoint

A bounded hole persists to the right at any mass-saturating time. Therefore,
if a descendant is still present at its finite lifetime endpoint, the cluster
has a strict mass deficit and has touched the unit boundary at that time. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- A bounded complementary component persists on a right neighborhood of
any positive time at which the cluster has its prescribed mass. -/
theorem ae_cluster_hole_persists_of_mass_eq
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, t ≤ s → s < t + δ →
      ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        Bornology.IsBounded V ∧ V ⊆ U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hopen hmono hmass hnull
  obtain ⟨r₀, hr₀, hvol⟩ := (hV.2 1 zero_lt_one).2.2
  intro t ht z hz heq U hU hUb
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hUdisc := bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hUb
  obtain ⟨p, hp, hUeq⟩ := hU
  have hpU : p ∈ U := hUeq ▸ mem_connectedComponentIn hp
  have hUopen : IsOpen U := by
    rw [← hUeq]
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hUopen.inter isOpen_ball)
    p ⟨hpU, hUdisc hpU⟩
  let r := min ε (r₀ / 2)
  have hr : 0 < r := lt_min hε (half_pos hr₀)
  have hrr : r < r₀ := (min_le_right _ _).trans_lt (half_lt_self hr₀)
  have hball : ball p r ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans (hεsub.trans inter_subset_left)
  have hdisc : ball p r ⊆ ball (0 : ℂ) 1 :=
    (ball_subset_ball (min_le_left _ _)).trans (hεsub.trans inter_subset_right)
  have hsmall (s : ℝ) (hs : s < t + r ^ βm) :
      ENNReal.ofReal (s - t) < μ ω (ball p r) := by
    have hs' : s - t < r ^ βm := by linarith
    exact ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hr βm)).mpr hs').trans_le
      (hvol r hr hrr p (hUdisc hpU)).1
  refine ⟨r ^ βm, Real.rpow_pos_of_pos hr βm, ?_⟩
  intro s hts hs
  obtain ⟨V, hVc, hVU, _⟩ := cluster_complement_component_persists_of_ball_mass
    (μ ω) ht.le hts (hopen t 1 ht zero_lt_one z hz).1
    (hopen s 1 (lt_of_lt_of_le ht hts) zero_lt_one z hz).1
    (hmono t s 1 ht hts zero_lt_one z hz) heq
    (hmass 1 s zero_lt_one (lt_of_lt_of_le ht hts) z hz).1
    (hnull s (lt_of_lt_of_le ht hts) z hz) ⟨p, hp, hUeq⟩ hball hdisc (hsmall s hs)
  exact ⟨V, hVc, hUb.subset hVU, hVU⟩

/-- A bounded hole of a compactly contained cluster has a finite lifetime.
If a descendant remains at the endpoint, the endpoint cluster has strict
mass deficit and its closure meets the unit circle. No existence of holes is asserted. -/
theorem ae_cluster_hole_lifetime_endpoint_mass_deficit
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
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        ((∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z L))ᶜ, V ⊆ U) →
          μ ω (cluster (μ ω) 1 z L) < ENNReal.ofReal L ∧
          ¬ closure (cluster (μ ω) 1 z L) ⊆ ball 0 1) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_bounded_hole_has_finite_lifetime hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_hole_persists_of_mass_eq hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hlife hpersist hmass hnull
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  rintro ⟨V, hV, hVU⟩
  have hL : 0 < L := ht.trans htL
  have hle := (hmass 1 L zero_lt_one hL z hz).1
  have hlt : μ ω (cluster (μ ω) 1 z L) < ENNReal.ofReal L := by
    apply lt_of_le_of_ne hle
    intro heq
    obtain ⟨δ, hδ, hp⟩ := hpersist L hL z hz heq V hV (hUb.subset hVU)
    have hLs : L < L + δ / 2 := lt_add_of_pos_right L (half_pos hδ)
    have hs : L + δ / 2 < L + δ := add_lt_add_of_le_of_lt le_rfl (half_lt_self hδ)
    obtain ⟨W, hW, _, hWV⟩ := hp (L + δ / 2) hLs.le hs
    exact hafter (L + δ / 2) hLs ⟨W, hW, hWV.trans hVU⟩
  refine ⟨hlt, ?_⟩
  intro hclL
  have hfront : μ ω (frontier (cluster (μ ω) 1 z L)) = 0 := by
    apply measure_mono_null _ (hnull L hL z hz)
    intro x hx
    exact ⟨hx, hclL (frontier_subset_closure hx)⟩
  have heq := (hmass 1 L zero_lt_one hL z hz).2.2 hclL hfront
  exact (ne_of_lt hlt) heq

end HarmonicBalls
