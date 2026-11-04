import HarmonicBalls.Proofs.Sec10.HoleLifetime
import Mathlib.Order.Interval.Set.OrdConnected

/-! # Times at which a point lies in a hole

For increasing closed clusters, a point cannot return to the exterior after
entering a bounded complementary component. Until it is swallowed, its later
component is contained in the original hole. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- A point that remains outside a larger set stays in a bounded complementary
component after entering a bounded complementary component of the smaller set. -/
theorem bounded_complement_component_mono_at_point
    {K L : Set ℂ} {x : ℂ} (hKL : K ⊆ L) (hxL : x ∈ Lᶜ)
    (hb : Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    x ∈ connectedComponentIn Lᶜ x ∧
      connectedComponentIn Lᶜ x ⊆ connectedComponentIn Kᶜ x ∧
      Bornology.IsBounded (connectedComponentIn Lᶜ x) := by
  have hsub := connectedComponentIn_mono x (compl_subset_compl.mpr hKL)
  exact ⟨mem_connectedComponentIn hxL, hsub, hb.subset hsub⟩

/-- For an increasing family of sets, the times at which a fixed point lies in
a bounded complementary component form an order-connected set. -/
theorem hole_times_ordConnected {F : ℝ → Set ℂ} {x : ℂ}
    (hmono : Monotone F) :
    {t : ℝ | x ∈ (F t)ᶜ ∧ Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}.OrdConnected := by
  apply ordConnected_iff.mpr
  intro t ht s hs hts r hr
  have hxr : x ∈ (F r)ᶜ := (compl_subset_compl.mpr (hmono hr.2)) hs.1
  exact ⟨hxr, (bounded_complement_component_mono_at_point (hmono hr.1) hxr ht.2).2.2⟩

universe u

/-- Under I2, after a point enters a bounded cluster-complement component, its
later component remains in that component for as long as the point stays
outside the closed cluster. The conclusion is simultaneous in all parameters. -/
theorem ae_cluster_hole_component_mono_at_point
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t s : ℝ, 0 < t → t ≤ s → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ x ∈ (closure (cluster (μ ω) 1 z s))ᶜ,
      Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x) →
      connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x ⊆
        connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x ∧
      Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro t s ht hts z hz x hx hb
  exact (bounded_complement_component_mono_at_point
    (closure_mono (hmono t s 1 ht hts zero_lt_one z hz)) hx hb).2

/-- Under I2, for every pole and point, the positive times when the point is
in a bounded cluster-complement component form an interval. No existence of
such a time, or assertion about either endpoint, is made. -/
theorem ae_cluster_hole_times_ordConnected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ x : ℂ,
      {t : ℝ | 0 < t ∧ x ∈ (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x)}.OrdConnected := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz x
  apply ordConnected_iff.mpr
  intro t ht s hs hts r hr
  have hrpos : 0 < r := ht.1.trans_le hr.1
  have hxr : x ∈ (closure (cluster (μ ω) 1 z r))ᶜ :=
    (compl_subset_compl.mpr (closure_mono (hmono r s 1 hrpos hr.2 zero_lt_one z hz))) hs.2.1
  exact ⟨hrpos, hxr, (bounded_complement_component_mono_at_point
    (closure_mono (hmono t r 1 ht.1 hr.1 zero_lt_one z hz)) hxr ht.2.2).2.2⟩

/-- Under I2, each point's set of positive hole times is a bounded interval.
The interval may be empty; neither endpoint is asserted to belong to it. -/
theorem ae_cluster_hole_times_bddAbove_ordConnected
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ x : ℂ,
      let S := {t : ℝ | 0 < t ∧ x ∈ (closure (cluster (μ ω) 1 z t))ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x)}
      S.OrdConnected ∧ BddAbove S := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_cluster_hole_times_ordConnected hI2
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hV hinterval
  intro z hz x
  refine ⟨hinterval z hz x, ?_⟩
  by_cases hx : x ∈ ball (0 : ℂ) 1
  · obtain ⟨T, hT, hentry⟩ := exists_cluster_contains_compact_of_volumeGrowth
      hV.1 zero_lt_one (hV.2 1 zero_lt_one) hz (isCompact_singleton : IsCompact ({x} : Set ℂ))
      (singleton_subset_iff.mpr hx)
    refine ⟨T, ?_⟩
    intro t ht
    apply le_of_not_gt
    intro hTt
    have hxC : x ∈ cluster (μ ω) 1 z t := hentry t hTt.le (mem_singleton x)
    exact ht.2.1 (subset_closure hxC)
  · refine ⟨0, ?_⟩
    intro t ht
    have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
    have hU : connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x ∈
        connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ := ⟨x, ht.2.1, rfl⟩
    have hxU := mem_connectedComponentIn ht.2.1
    exact (hx (bounded_complement_component_subset_unit_ball isClosed_closure hcl hU ht.2.2 hxU)).elim

end HarmonicBalls
