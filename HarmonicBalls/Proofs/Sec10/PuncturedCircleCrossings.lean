import HarmonicBalls.Proofs.Sec10.ConnectedSphereCrossings
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Crossing bounds from sparse circular frontier contacts -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

universe u

/-- Removing one point from the unit circle leaves a preconnected set. -/
theorem isPreconnected_unit_sphere_sdiff_singleton {v : ℂ} (hv : ‖v‖ = 1) :
    IsPreconnected (sphere (0 : ℂ) 1 \ {v}) := by
  let f := (stereographic hv).symm
  have hf : Continuous f := (isOpenEmbedding_stereographic_symm hv).continuous
  have hcont : Continuous (fun x => ((f x : sphere (0 : ℂ) 1) : ℂ)) :=
    continuous_subtype_val.comp hf
  have hrange : Set.range (fun x => ((f x : sphere (0 : ℂ) 1) : ℂ)) =
      sphere (0 : ℂ) 1 \ {v} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hn : f y ≠ ⟨v, by simpa using hv⟩ := by
        have := (show f y ∈ Set.range f from ⟨y, rfl⟩)
        rw [range_stereographic_symm hv] at this
        simpa using this
      exact ⟨(f y).property, by simpa using fun h => hn (Subtype.ext h)⟩
    · rintro ⟨hx, hxv⟩
      have hx' : (⟨x, hx⟩ : sphere (0 : ℂ) 1) ∈ Set.range f := by
        rw [range_stereographic_symm hv]
        simpa using hxv
      obtain ⟨y, hy⟩ := hx'
      exact ⟨y, congrArg Subtype.val hy⟩
  rw [← hrange]
  exact isPreconnected_range hcont

/-- Every punctured circle in the plane is preconnected. -/
theorem isPreconnected_sphere_sdiff_singleton (w a : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (sphere w r \ {a}) := by
  by_cases ha : a ∈ sphere w r
  · let e : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft w)
    have he : e '' sphere (0 : ℂ) 1 = sphere w r := by
      change (fun x : ℂ => w + r • x) '' sphere 0 1 = sphere w r
      rw [← image_image]
      change (fun x : ℂ => w + x) '' (r • sphere (0 : ℂ) 1) = _
      rw [smul_sphere' hr.ne']
      simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mem_sphere, dist_eq_norm] using hy
      · intro hx
        refine ⟨x - w, ?_, by abel⟩
        simpa [mem_sphere, dist_eq_norm] using hx
    let v := e.symm a
    have hv_mem : v ∈ sphere (0 : ℂ) 1 := by
      obtain ⟨x, hx, hxa⟩ : a ∈ e '' sphere (0 : ℂ) 1 := he ▸ ha
      simpa [v, ← hxa] using hx
    have hv : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv_mem
    have himage : e '' (sphere (0 : ℂ) 1 \ {v}) = sphere w r \ {a} := by
      rw [Set.image_sdiff e.injective, he, Set.image_singleton]
      simp [v]
    rw [← himage]
    exact (isPreconnected_unit_sphere_sdiff_singleton hv).image e e.continuous.continuousOn
  · have heq : sphere w r \ {a} = sphere w r := sdiff_eq_left.mpr (by
      simpa [disjoint_singleton_right] using ha)
    rw [heq]
    exact (isConnected_sphere (by simp) w hr.le).isPreconnected

/-- If an intermediate circle meets the frontier in at most one point, an
open set has at most one crossing component. -/
theorem encard_crossingComponents_le_one_of_sphere_frontier_subset_singleton
    {G : Set ℂ} (hG : IsOpen G) {w a : ℂ} {r s R : ℝ}
    (hs : 0 < s) (hrs : r < s) (hsR : s < R) (hr : 0 ≤ r)
    (hfront : sphere w s ∩ frontier G ⊆ {a}) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  by_cases haG : a ∈ G
  · have hdis : Disjoint (sphere w s) (frontier G) := by
      rw [disjoint_left]
      intro p hp hpf
      have hpa : p = a := mem_singleton_iff.mp (hfront ⟨hp, hpf⟩)
      subst p
      rw [hG.frontier_eq] at hpf
      exact hpf.2 haG
    exact encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
      hG hr hrs hsR hdis
  · let P := sphere w s \ {a}
    have hP : IsPreconnected P := isPreconnected_sphere_sdiff_singleton w a hs
    have hdis : Disjoint P (frontier G) := by
      rw [disjoint_left]
      intro p hp hpf
      exact hp.2 (hfront ⟨hp.1, hpf⟩)
    rcases IsPreconnected.subset_or_disjoint_of_disjoint_frontier hP hG hdis with hsub | hdisG
    · have heq : G ∩ sphere w s = P := by
        ext p
        constructor
        · rintro ⟨hpG, hps⟩
          refine ⟨hps, ?_⟩
          intro hpa
          have : p = a := mem_singleton_iff.mp hpa
          subst p
          exact haG hpG
        · intro hp
          exact ⟨hsub hp, hp.1⟩
      exact encard_crossingComponents_le_one_of_preconnected_sphere_inter hrs hsR (heq ▸ hP)
    · have hempty : G ∩ sphere w s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro p ⟨hpG, hps⟩
        have hpa : p ≠ a := by rintro rfl; exact haG hpG
        exact disjoint_left.mp hdisG ⟨hps, by simpa using hpa⟩ hpG
      exact encard_crossingComponents_le_one_of_preconnected_sphere_inter hrs hsR
        (hempty ▸ isPreconnected_empty)

/-- At the selected exact radius, excess crossings require a nearby pole and
at least two distinct frontier points on every intermediate circle. The
field-scaling inputs remain staged pending source review. -/
theorem ae_boundary_free_excess_crossings_force_two_frontier_points
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (⌈1 / α⌉₊ : ℕ∞) <
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard →
        dist z w ≤ ρ + ρ / 50 ∧
        ∀ s ∈ Ioo (ρ / 3) (2 * ρ),
          ∃ a ∈ sphere w s ∩ frontier (cluster (μ ω) 1 z t),
          ∃ b ∈ sphere w s ∩ frontier (cluster (μ ω) 1 z t), b ≠ a := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_boundary_free_excess_crossings_force_frontier_crossing hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound hopen
  filter_upwards [hbound, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hexcess
  obtain ⟨hnear, _, hmeet, _⟩ := hρbound z t ht hcl hexcess
  have hz : z ∈ ball (0 : ℂ) 1 := by
    by_contra hn
    have hempty := cluster_eq_empty_of_pole_not_mem (μ := μ ω) hn ht.le
    simp [hempty, crossingComponents, connectedComponentsIn] at hexcess
  have hceil : (1 : ℕ∞) ≤ ⌈1 / α⌉₊ := by
    exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1))
  refine ⟨hnear, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := hmeet s hs
  refine ⟨a, ha, ?_⟩
  by_contra hn
  have hsub : sphere w s ∩ frontier (cluster (μ ω) 1 z t) ⊆ {a} := by
    intro b hb
    have hba : b = a := by
      by_contra hne
      exact hn ⟨b, hb, hne⟩
    simpa using hba
  have hspos : 0 < s := (by positivity : 0 < ρ / 3).trans hs.1
  have hone := encard_crossingComponents_le_one_of_sphere_frontier_subset_singleton
    (hopen t 1 ht zero_lt_one z hz).1 hspos hs.1 hs.2 (by positivity) hsub
  exact (not_le_of_gt hexcess) (hone.trans hceil)

end HarmonicBalls
