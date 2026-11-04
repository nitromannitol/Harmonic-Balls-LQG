import HarmonicBalls.Proofs.Sec10.BoundaryFreeFrontierCrossings

/-!
# Crossing components and connected circular sections

If an intermediate circular section of a set is preconnected, all crossing
components meet the same component of the outer ball. This applies even when
the section is a proper subset of the circle and meets the frontier.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A preconnected intermediate circular section allows at most one crossing. -/
theorem encard_crossingComponents_le_one_of_preconnected_sphere_inter
    {G : Set ℂ} {w : ℂ} {r s R : ℝ} (hrs : r < s) (hsR : s < R)
    (hsection : IsPreconnected (G ∩ sphere w s)) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  let F := G ∩ ball w R
  let S := crossingComponents F w r R
  by_cases hS : S.Nonempty
  · obtain ⟨C, hC⟩ := hS
    obtain ⟨p, hp, rfl⟩ := hC.1
    have hpre : IsPreconnected (connectedComponentIn F p) := isPreconnected_connectedComponentIn
    obtain ⟨x, hxC, hxs⟩ := IsPreconnected.exists_mem_sphere_of_crosses hpre hrs hsR hC.2
    have hxF : x ∈ F := connectedComponentIn_subset F p hxC
    have hxsection : x ∈ G ∩ sphere w s := ⟨hxF.1, hxs⟩
    have hsectionF : G ∩ sphere w s ⊆ F := by
      intro y hy
      exact ⟨hy.1, mem_ball.mpr (by rw [mem_sphere.mp hy.2]; exact hsR)⟩
    have hsectionC : G ∩ sphere w s ⊆ connectedComponentIn F p := by
      have h := hsection.subset_connectedComponentIn hxsection hsectionF
      rw [← connectedComponentIn_eq hxC] at h
      exact h
    have hsub : S ⊆ {connectedComponentIn F p} := by
      intro D hD
      obtain ⟨q, hq, rfl⟩ := hD.1
      have hDpre : IsPreconnected (connectedComponentIn F q) := isPreconnected_connectedComponentIn
      obtain ⟨y, hyD, hys⟩ := IsPreconnected.exists_mem_sphere_of_crosses hDpre hrs hsR hD.2
      have hyF : y ∈ F := connectedComponentIn_subset F q hyD
      have hyC := hsectionC ⟨hyF.1, hys⟩
      simpa only [mem_singleton_iff] using
        (connectedComponentIn_eq hyD).trans (connectedComponentIn_eq hyC).symm
    exact (Set.encard_mono hsub).trans (by simp)
  · have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    change S.encard ≤ 1
    rw [hempty]
    simp

/-- Distinct crossing components meet distinct connected components of any
intermediate circular section. -/
theorem encard_crossingComponents_le_sphere_inter_components
    (G : Set ℂ) (w : ℂ) {r s R : ℝ} (hrs : r < s) (hsR : s < R) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤
      (connectedComponentsIn (G ∩ sphere w s)).encard := by
  classical
  let F := G ∩ ball w R
  let T := G ∩ sphere w s
  let S := crossingComponents F w r R
  have hTF : T ⊆ F := by
    intro x hx
    exact ⟨hx.1, mem_ball.mpr (by rw [mem_sphere.mp hx.2]; exact hsR)⟩
  have hex : ∀ C ∈ S, ∃ D ∈ connectedComponentsIn T, D ⊆ C := by
    intro C hC
    obtain ⟨p, hp, hpC⟩ := hC.1
    have hpre : IsPreconnected C := by
      rw [← hpC]
      exact isPreconnected_connectedComponentIn
    obtain ⟨x, hxC, hxs⟩ :=
      IsPreconnected.exists_mem_sphere_of_crosses hpre hrs hsR hC.2
    have hxF : x ∈ F := connectedComponentIn_subset F p (hpC ▸ hxC)
    have hxT : x ∈ T := ⟨hxF.1, hxs⟩
    refine ⟨connectedComponentIn T x, ⟨x, hxT, rfl⟩, ?_⟩
    rw [← hpC]
    exact connectedComponentIn_mono_of_mem hTF hxT (hpC ▸ hxC)
  let pick : Set ℂ → Set ℂ := fun C => if hC : C ∈ S then
    Classical.choose (hex C hC) else ∅
  have hpick : ∀ C ∈ S, pick C ∈ connectedComponentsIn T ∧ pick C ⊆ C := by
    intro C hC
    simpa [pick, hC] using Classical.choose_spec (hex C hC)
  apply Set.encard_le_encard_of_injOn (fun C hC => (hpick C hC).1)
  intro C hC D hD heq
  by_contra hne
  have hdisj := pairwiseDisjoint_connectedComponentsIn F hC.1 hD.1 hne
  obtain ⟨x, hx, heqx⟩ := (hpick C hC).1
  have hxpick : x ∈ pick C := heqx ▸ mem_connectedComponentIn hx
  exact Set.disjoint_left.mp hdisj ((hpick C hC).2 hxpick)
    ((hpick D hD).2 (heq ▸ hxpick))

/-- At the selected exact radius, a bound on the number of components of an
intermediate circular section or pole separation gives the crossing bound.
The field-scaling inputs are staged pending source review. -/
theorem ae_boundary_free_crossings_of_section_components_or_pole_margin
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
        ((∃ s ∈ Ioo (ρ / 3) (2 * ρ),
          (connectedComponentsIn (cluster (μ ω) 1 z t ∩ sphere w s)).encard ≤
            ⌈1 / α⌉₊) ∨
          ρ + ρ / 50 < dist z w) →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_without_boundary_margin_exact_all_poles hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound
  filter_upwards [hbound] with ε hbound
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hcase
  rcases hcase with ⟨s, hs, hsection⟩ | hpole
  · exact (encard_crossingComponents_le_sphere_inter_components
      (cluster (μ ω) 1 z t) w hs.1 hs.2).trans hsection
  · exact hρbound z t ht hcl hpole

end HarmonicBalls
