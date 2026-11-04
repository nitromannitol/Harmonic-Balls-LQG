import HarmonicBalls.Proofs.Sec10.LocalFrontierLength
import HarmonicBalls.Proofs.Sec10.PuncturedCircleCrossings

/-! # Uniform two-sided contacts of complementary frontiers -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal MeasureTheory

/-- A circle meeting both disjoint open sides of a common frontier meets the
frontier in at least two points. -/
theorem sphere_frontier_two_contacts_of_two_sides
    {G U : Set ℂ} (hGo : IsOpen G) (hUo : IsOpen U)
    (hdis : Disjoint G U) (hfront : frontier U ⊆ frontier G)
    {p x y : ℂ} {s : ℝ} (hs : 0 < s)
    (hxG : x ∈ G) (hxS : x ∈ sphere p s) (hyU : y ∈ U) (hyS : y ∈ sphere p s) :
    ∃ a ∈ sphere p s ∩ frontier U, ∃ b ∈ sphere p s ∩ frontier U, a ≠ b := by
  have hxU : x ∉ U := fun h => disjoint_left.mp hdis hxG h
  have hmeet : (sphere p s ∩ frontier U).Nonempty := by
    by_contra hn
    have havoid : sphere p s ⊆ (frontier U)ᶜ := by
      intro q hq hqf
      exact hn ⟨q, hq, hqf⟩
    have hycomp := (isConnected_sphere (by simp) p hs.le).isPreconnected.subset_connectedComponentIn
      hxS havoid hyS
    exact not_mem_connectedComponentIn_compl_frontier hUo hxU (havoid hxS) hyU hycomp
  obtain ⟨a, haS, haf⟩ := hmeet
  have haG : a ∉ G := by
    have ha := hfront haf
    rw [hGo.frontier_eq] at ha
    exact ha.2
  have haU : a ∉ U := by
    have ha := haf
    rw [hUo.frontier_eq] at ha
    exact ha.2
  have hxa : x ≠ a := by rintro rfl; exact haG hxG
  have hya : y ≠ a := by rintro rfl; exact haU hyU
  have hsecond : ((sphere p s \ {a}) ∩ frontier U).Nonempty := by
    by_contra hn
    have havoid : sphere p s \ {a} ⊆ (frontier U)ᶜ := by
      intro q hq hqf
      exact hn ⟨q, hq, hqf⟩
    have hxp : x ∈ sphere p s \ {a} := ⟨hxS, by simpa using hxa⟩
    have hyp : y ∈ sphere p s \ {a} := ⟨hyS, by simpa using hya⟩
    have hycomp := (isPreconnected_sphere_sdiff_singleton p a hs).subset_connectedComponentIn
      hxp havoid hyp
    exact not_mem_connectedComponentIn_compl_frontier hUo hxU (havoid hxp) hyU hycomp
  obtain ⟨b, ⟨hbS, hbne⟩, hbf⟩ := hsecond
  exact ⟨a, ⟨haS, haf⟩, b, ⟨hbS, hbf⟩, by simpa [eq_comm] using hbne⟩

/-- The two-contact radius can be chosen uniformly over the whole common
frontier of two disjoint connected open sets. -/
theorem uniform_frontier_two_contacts_of_two_sides
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ frontier U, ∀ s ∈ Ioo (0 : ℝ) R,
      ∃ a ∈ sphere p s ∩ frontier U, ∃ b ∈ sphere p s ∩ frontier U, a ≠ b := by
  obtain ⟨x, hxG⟩ := hGc.nonempty
  obtain ⟨y, hyU⟩ := hUc.nonempty
  obtain ⟨rx, hrx, hxball⟩ := Metric.mem_nhds_iff.mp (hGo.mem_nhds hxG)
  obtain ⟨ry, hry, hyball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hyU)
  refine ⟨min rx ry, lt_min hrx hry, ?_⟩
  intro p hp s hs
  have hpG : p ∉ G := by
    have h := hfront hp
    rw [hGo.frontier_eq] at h
    exact h.2
  have hpU : p ∉ U := by
    have h := hp
    rw [hUo.frontier_eq] at h
    exact h.2
  have hxp : rx ≤ dist x p := by
    by_contra h
    apply hpG
    exact hxball (mem_ball.mpr (by simpa [dist_comm] using lt_of_not_ge h))
  have hyp : ry ≤ dist y p := by
    by_contra h
    apply hpU
    exact hyball (mem_ball.mpr (by simpa [dist_comm] using lt_of_not_ge h))
  have hsx : s < dist x p := (lt_of_lt_of_le hs.2 (min_le_left _ _)).trans_le hxp
  have hsy : s < dist y p := (lt_of_lt_of_le hs.2 (min_le_right _ _)).trans_le hyp
  obtain ⟨a, haG, haS⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hGc.isPreconnected
    (frontier_subset_closure (hfront hp)) hxG hs.1 hsx
  obtain ⟨b, hbU, hbS⟩ := IsPreconnected.exists_mem_sphere_of_mem_closure hUc.isPreconnected
    (frontier_subset_closure hp) hyU hs.1 hsy
  exact sphere_frontier_two_contacts_of_two_sides hGo hUo hdis hfront hs.1 haG haS hbU hbS

/-- One radius works at every point of a common frontier for the local
Hausdorff-length lower bound. -/
theorem uniform_frontier_local_length_ge_of_two_sides
    {G U : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G)
    (hUo : IsOpen U) (hUc : IsConnected U) (hdis : Disjoint G U)
    (hfront : frontier U ⊆ frontier G) :
    ∃ R : ℝ, 0 < R ∧ ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r → r ≤ R →
      ENNReal.ofReal r ≤ μH[1] (frontier U ∩ ball p r) := by
  obtain ⟨R, hR, hcontact⟩ := uniform_frontier_two_contacts_of_two_sides
    hGo hGc hUo hUc hdis hfront
  refine ⟨R, hR, ?_⟩
  intro p hp r hr hrR
  have h := hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres
    (F := frontier U) (w := p) (r := 0) (R := r) (by
      intro s hs
      obtain ⟨a, ha, _, _, _⟩ := hcontact p hp s ⟨hs.1, hs.2.trans_le hrR⟩
      exact ⟨a, ha⟩)
  have hsub : frontier U ∩ {x | (0 : ℝ) < dist x p ∧ dist x p < r} ⊆
      frontier U ∩ ball p r := by
    intro q hq
    exact ⟨hq.1, mem_ball.mpr hq.2.2⟩
  simpa using h.trans (measure_mono hsub)

universe u

/-- Under volume growth, every complementary frontier admits a uniform
positive scale on which every centered circle meets it at least twice and
every centered ball has frontier length at least its radius. -/
theorem ae_cluster_complement_frontier_uniform_contacts_and_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∃ R : ℝ, 0 < R ∧ ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r → r < R →
        (∃ a ∈ sphere p r ∩ frontier U, ∃ b ∈ sphere p r ∩ frontier U, a ≠ b) ∧
        ENNReal.ofReal r ≤ μH[1] (frontier U ∩ ball p r) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU
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
  obtain ⟨R, hR, hcontact⟩ := uniform_frontier_two_contacts_of_two_sides
    hc.1 hc.2.1 hg.1 hg.2.1 hdis hg.2.2.2.1
  obtain ⟨S, hS, hlength⟩ := uniform_frontier_local_length_ge_of_two_sides
    hc.1 hc.2.1 hg.1 hg.2.1 hdis hg.2.2.2.1
  refine ⟨min R S, lt_min hR hS, ?_⟩
  intro p hp r hr hrmin
  exact ⟨hcontact p hp r ⟨hr, hrmin.trans_le (min_le_left _ _)⟩,
    hlength p hp r hr (le_of_lt (hrmin.trans_le (min_le_right _ _)))⟩

end HarmonicBalls
