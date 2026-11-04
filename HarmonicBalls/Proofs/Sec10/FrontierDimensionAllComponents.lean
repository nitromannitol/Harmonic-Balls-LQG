import HarmonicBalls.Proofs.Sec10.FrontierHausdorffDimension
import HarmonicBalls.Proofs.Sec10.ExteriorComponent

/-! # Length of every complementary frontier

Bounded complementary components and the exterior component are treated
separately. No connectedness of the entire complement is assumed.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal MeasureTheory

/-- A bounded set containing a ball has frontier length at least the ball's
horizontal diameter. -/
theorem hausdorffMeasure_one_frontier_ge_of_bounded
    {U : Set ℂ} (hUb : Bornology.IsBounded U) {p : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : ball p r ⊆ U) :
    ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U) := by
  obtain ⟨R, hR⟩ := hUb.closure.subset_ball (0 : ℂ)
  exact (hausdorffMeasure_one_frontier_ge_of_ball_subset isClosed_closure hr
    (hball.trans subset_closure) hR).trans (measure_mono frontier_closure_subset)

/-- If an open set has bounded complement, any ball in the complement gives
a lower bound on the length of its frontier. -/
theorem hausdorffMeasure_one_frontier_ge_of_bounded_compl
    {U : Set ℂ} (hUo : IsOpen U) (hUb : Bornology.IsBounded Uᶜ)
    {p : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ Uᶜ) :
    ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U) := by
  obtain ⟨R, hR⟩ := hUb.subset_ball (0 : ℂ)
  simpa only [frontier_compl] using
    hausdorffMeasure_one_frontier_ge_of_ball_subset hUo.isClosed_compl hr hball hR

/-- A complementary component of a closed set inside the unit disk is either
bounded, or has bounded complement. -/
theorem bounded_or_bounded_compl_component
    {K U : Set ℂ} (hK : K ⊆ ball 0 1) (hU : U ∈ connectedComponentsIn Kᶜ) :
    Bornology.IsBounded U ∨ Bornology.IsBounded Uᶜ := by
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  let V := connectedComponentIn Kᶜ (2 : ℂ)
  by_cases heq : U = V
  · right
    have hext : (closedBall (0 : ℂ) 1)ᶜ ⊆ Kᶜ :=
      compl_subset_compl.mpr (hK.trans ball_subset_closedBall)
    have hsub : (closedBall (0 : ℂ) 1)ᶜ ⊆ U := by
      rw [heq]
      exact (isPreconnected_compl_closedBall_complex 0 zero_lt_one).subset_connectedComponentIn
        hp hext
    have hsub' : Uᶜ ⊆ closedBall (0 : ℂ) 1 := by
      simpa using compl_subset_compl.mpr hsub
    exact (isCompact_closedBall (0 : ℂ) 1).isBounded.subset hsub'
  · left
    exact (isCompact_closedBall (0 : ℂ) 1).isBounded.subset
      (component_compl_subset_closedBall_of_ne_exterior zero_lt_one
        (hK.trans ball_subset_closedBall) hp hU heq)

/-- A component of the complement of the closure of a nonempty bounded open
set has positive frontier length and frontier dimension at least one. -/
theorem component_frontier_positive_length_and_dimH
    {G U : Set ℂ} (hGo : IsOpen G) (hGne : G.Nonempty)
    (hcl : closure G ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn (closure G)ᶜ) :
    (∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U)) ∧
      1 ≤ dimH (frontier U) := by
  obtain ⟨p, hp, hUeq⟩ := hU
  have hUo : IsOpen U := by rw [← hUeq]; exact isClosed_closure.isOpen_compl.connectedComponentIn
  have hUne : U.Nonempty := ⟨p, by rw [← hUeq]; exact mem_connectedComponentIn hp⟩
  have hUs : U ⊆ (closure G)ᶜ := by rw [← hUeq]; exact connectedComponentIn_subset _ _
  have hGsub : G ⊆ Uᶜ := by
    intro q hq hqU
    exact hUs hqU (subset_closure hq)
  have hbound := bounded_or_bounded_compl_component hcl ⟨p, hp, hUeq⟩
  have hlen : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U) := by
    rcases hbound with hb | hb
    · obtain ⟨q, hq⟩ := hUne
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hq)
      exact ⟨r, hr, hausdorffMeasure_one_frontier_ge_of_bounded hb hr hball⟩
    · obtain ⟨q, hq⟩ := hGne
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hGo.mem_nhds hq)
      exact ⟨r, hr, hausdorffMeasure_one_frontier_ge_of_bounded_compl hUo hb hr
        (hball.trans hGsub)⟩
  refine ⟨hlen, ?_⟩
  obtain ⟨r, hr, hlen⟩ := hlen
  apply le_dimH_of_hausdorffMeasure_ne_zero (d := 1)
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hlen)

universe u

/-- Volume growth alone gives positive length and Hausdorff dimension at
least one for every complementary frontier of every compactly contained
cluster. This includes bounded complementary components. -/
theorem ae_cluster_complement_frontier_positive_length_and_dimH
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        (∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U)) ∧
          1 ≤ dimH (frontier U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω hcluster
  intro t ht z hz hcl U hU
  have hG := hcluster t 1 ht zero_lt_one z hz
  exact component_frontier_positive_length_and_dimH hG.1 hG.2.1.nonempty hcl hU

end HarmonicBalls
