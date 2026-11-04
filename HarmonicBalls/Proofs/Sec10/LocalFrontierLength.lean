import HarmonicBalls.Proofs.Sec10.FrontierHausdorffMeasure
import HarmonicBalls.Proofs.Sec10.FrontierNoIsolatedPoints
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Local length of complementary frontiers -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal MeasureTheory

/-- A connected set approaching a point and reaching beyond a circle meets
that circle. -/
theorem IsPreconnected.exists_mem_sphere_of_mem_closure
    {C : Set ℂ} (hC : IsPreconnected C) {p x : ℂ}
    (hp : p ∈ closure C) (hx : x ∈ C) {s : ℝ} (hs : 0 < s)
    (hfar : s < dist x p) : ∃ q ∈ C, q ∈ sphere p s := by
  obtain ⟨a, haball, ha⟩ := mem_closure_iff.mp hp _ isOpen_ball (mem_ball_self hs)
  obtain ⟨q, hq, hd⟩ := hC.intermediate_value ha hx
    (continuous_id.dist continuous_const).continuousOn
    ⟨(mem_ball.mp haball).le, hfar.le⟩
  exact ⟨q, hq, mem_sphere.mpr hd⟩

/-- Near a common frontier point of two disjoint connected open sets, the
frontier meets every sufficiently small circle. -/
theorem frontier_meets_small_spheres_of_two_sides
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {p : ℂ} (hp : p ∈ frontier U) :
    ∃ R : ℝ, 0 < R ∧ ∀ s ∈ Ioo (0 : ℝ) R, (sphere p s ∩ frontier U).Nonempty := by
  obtain ⟨x, hx⟩ := hGc.nonempty
  obtain ⟨y, hy⟩ := hUc.nonempty
  have hpG : p ∉ G := by
    have h := hfront hp
    rw [hGo.frontier_eq] at h
    exact h.2
  have hpU : p ∉ U := by
    have h := hp
    rw [hUo.frontier_eq] at h
    exact h.2
  have hxne : x ≠ p := by rintro rfl; exact hpG hx
  have hyne : y ≠ p := by rintro rfl; exact hpU hy
  let R := min (dist x p) (dist y p)
  have hR : 0 < R := lt_min (dist_pos.mpr hxne) (dist_pos.mpr hyne)
  refine ⟨R, hR, ?_⟩
  intro s hs
  have hsx : s < dist x p := lt_of_lt_of_le hs.2 (min_le_left _ _)
  have hsy : s < dist y p := lt_of_lt_of_le hs.2 (min_le_right _ _)
  obtain ⟨a, haG, haS⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hGc.isPreconnected
    (frontier_subset_closure (hfront hp)) hx hs.1 hsx
  obtain ⟨b, hbU, hbS⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hUc.isPreconnected
    (frontier_subset_closure hp) hy hs.1 hsy
  by_contra hn
  have havoid : sphere p s ⊆ (frontier U)ᶜ := by
    intro q hq hqf
    exact hn ⟨q, hq, hqf⟩
  have hbcomp := (isConnected_sphere (by simp) p hs.1.le).isPreconnected.subset_connectedComponentIn
    haS havoid hbS
  have haU : a ∉ U := fun haU => disjoint_left.mp hdis haG haU
  exact not_mem_connectedComponentIn_compl_frontier hUo haU (havoid haS) hbU hbcomp

/-- Each sufficiently small neighborhood of a common frontier point has
Hausdorff length at least its radius. -/
theorem frontier_local_length_ge_of_two_sides
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) {p : ℂ} (hp : p ∈ frontier U) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      ENNReal.ofReal r ≤ μH[1] (frontier U ∩ ball p r) := by
  obtain ⟨R, hR, hmeet⟩ := frontier_meets_small_spheres_of_two_sides
    hGo hGc hUo hUc hdis hfront hp
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have h := hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres
    (F := frontier U) (w := p) (r := 0) (R := r)
    (fun s hs => hmeet s ⟨hs.1, lt_of_lt_of_le hs.2 hrR⟩)
  have hsub : frontier U ∩ {x | (0 : ℝ) < dist x p ∧ dist x p < r} ⊆
      frontier U ∩ ball p r := by
    intro q hq
    exact ⟨hq.1, mem_ball.mpr hq.2.2⟩
  simpa using h.trans (measure_mono hsub)

universe u

/-- Under volume growth, every point of every complementary cluster
frontier has the local Hausdorff-length lower bound. -/
theorem ae_cluster_complement_frontier_local_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ p ∈ frontier U, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
        ENNReal.ofReal r ≤ μH[1] (frontier U ∩ ball p r) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU p hp
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨v, hv, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (cluster (μ ω) 1 z t) U := by
    rw [disjoint_left]
    intro w hw hwU
    exact hUs hwU (subset_closure hw)
  exact frontier_local_length_ge_of_two_sides hc.1 hc.2.1 hg.1 hg.2.1 hdis hg.2.2.2.1 hp

/-- Every neighborhood of every complementary frontier point has
Hausdorff dimension at least one, under volume growth alone. -/
theorem ae_cluster_complement_frontier_local_dimH
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r →
        1 ≤ dimH (frontier U ∩ ball p r) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_complement_frontier_local_length hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hlocal
  intro t ht z hz hcl U hU p hp r hr
  obtain ⟨R, hR, hlength⟩ := hlocal t ht z hz hcl U hU p hp
  let s := min R r
  have hs : 0 < s := lt_min hR hr
  have hsr : s ≤ r := min_le_right _ _
  have hsR : s ≤ R := min_le_left _ _
  have hbound := hlength s hs hsR
  have hsub : frontier U ∩ ball p s ⊆ frontier U ∩ ball p r :=
    inter_subset_inter_right _ (ball_subset_ball hsr)
  have hpos : 0 < μH[1] (frontier U ∩ ball p r) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hs) (hbound.trans (measure_mono hsub))
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := 1) (ne_of_gt hpos)

end HarmonicBalls
