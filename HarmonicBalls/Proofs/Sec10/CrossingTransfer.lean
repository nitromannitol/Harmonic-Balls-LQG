import HarmonicBalls.Proofs.Sec10.CrossingLocalization
import HarmonicBalls.Proofs.Sec10.ComplementComponents

/-!
# Transferring crossing counts between complementary sets and clusters

This is the counting step in Proposition 10.6. The existence of an annular
crossing inside each ball crossing is a separate boundary-bumping obligation;
the containment of a cluster crossing in each complementary crossing is the
content of Lemma 10.5. Both are kept as explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- If each crossing component of `F` in the ball contains a crossing
component of `G` in that ball, then the crossing count for `F` is at most
that for `G`. -/
theorem encard_crossingComponents_le_of_containment
    (F G : Set ℂ) (w : ℂ) (r R : ℝ)
    (h : ∀ C ∈ crossingComponents F w r R,
      ∃ D ∈ crossingComponents G w r R, D ⊆ C) :
    (crossingComponents F w r R).encard ≤ (crossingComponents G w r R).encard := by
  classical
  let pick : Set ℂ → Set ℂ := fun C => if hC : C ∈ crossingComponents F w r R then
    Classical.choose (h C hC) else ∅
  have hpick : ∀ C ∈ crossingComponents F w r R,
      pick C ∈ crossingComponents G w r R ∧ pick C ⊆ C := by
    intro C hC
    simpa [pick, hC] using Classical.choose_spec (h C hC)
  apply Set.encard_le_encard_of_injOn (fun C hC => (hpick C hC).1)
  intro C hC D hD heq
  by_contra hne
  have hdisj := pairwiseDisjoint_connectedComponentsIn F hC.1 hD.1 hne
  obtain ⟨x, hx, heqx⟩ := (hpick C hC).1.1
  have hxpick : x ∈ pick C := by
    rw [← heqx]
    exact mem_connectedComponentIn hx
  have hxC : x ∈ C := (hpick C hC).2 hxpick
  have hxD : x ∈ D := (hpick D hD).2 (heq ▸ hxpick)
  exact Set.disjoint_left.mp hdisj hxC hxD

/-- The component-counting conclusion of Proposition 10.6 follows from
annular boundary bumping and the crossing containment asserted by Lemma 10.5. -/
theorem encard_ball_crossings_le_of_annular_containment
    (F G : Set ℂ) (hGF : G ⊆ F) (w : ℂ) (r R : ℝ)
    (hbump : ∀ C ∈ crossingComponents (F ∩ ball w R) w r R,
      ∃ D ∈ crossingComponents (F ∩ annulus w r R) w r R, D ⊆ C)
    (hcontain : ∀ D ∈ crossingComponents (F ∩ annulus w r R) w r R,
      ∃ E ∈ crossingComponents (G ∩ annulus w r R) w r R, E ⊆ D) :
    (crossingComponents (F ∩ ball w R) w r R).encard ≤
      (crossingComponents (G ∩ ball w R) w r R).encard := by
  apply encard_crossingComponents_le_of_containment
  intro C hC
  obtain ⟨D, hD, hDC⟩ := hbump C hC
  obtain ⟨E, hE, hED⟩ := hcontain D hD
  obtain ⟨x, hx, hxE⟩ := hE.1
  have hxE' : x ∈ E := by rw [← hxE]; exact mem_connectedComponentIn hx
  have hsub : G ∩ annulus w r R ⊆ G ∩ ball w R := by
    intro y hy
    exact ⟨hy.1, hy.2.1⟩
  have hxGB : x ∈ G ∩ ball w R := hsub hx
  let T := connectedComponentIn (G ∩ ball w R) x
  have hET : E ⊆ T := by
    rw [← hxE]
    exact connectedComponentIn_mono x hsub
  have hTC : T ⊆ C := by
    obtain ⟨y, hy, hyC⟩ := hC.1
    rw [← hyC]
    apply connectedComponentIn_mono_of_mem (show G ∩ ball w R ⊆ F ∩ ball w R from
      fun a ha => ⟨hGF ha.1, ha.2⟩) hxGB
    exact hyC ▸ hDC (hED hxE')
  have hcross : CrossesAnnulus T w r R := by
    obtain ⟨⟨a, ha, has⟩, ⟨b, hb, hbs⟩⟩ := hE.2
    exact ⟨⟨a, closure_mono hET ha, has⟩, ⟨b, closure_mono hET hb, hbs⟩⟩
  exact ⟨T, ⟨⟨x, hxGB, rfl⟩, hcross⟩, hTC⟩

universe u

/-- On the cluster geometry event, Lemma 10.5 and annular boundary bumping
bound complementary crossings by cluster crossings. -/
theorem ae_clusterComplement_crossings_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      closure (annulus w r R) ⊆ ball 0 1 →
      ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      (∀ C ∈ crossingComponents (Uᶜ ∩ ball w R) w r R,
        ∃ D ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R, D ⊆ C) →
      (crossingComponents (Uᶜ ∩ ball w R) w r R).encard ≤
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w R) w r R).encard := by
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
    hC hcirc μ hGFF hμ hI2, h5 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcross
  intro w r R hr hrR hann t ht z hz hcl U hU hbump
  have hgeo := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hsub : cluster (μ ω) 1 z t ⊆ Uᶜ := by
    obtain ⟨x, hx, hxU⟩ := hU
    intro y hy hyU
    have hyK : y ∈ closure (cluster (μ ω) 1 z t) := subset_closure hy
    have hyKc : y ∈ (closure (cluster (μ ω) 1 z t))ᶜ :=
      connectedComponentIn_subset _ x (hxU ▸ hyU)
    exact hyKc hyK
  apply encard_ball_crossings_le_of_annular_containment _ _ hsub w r R hbump
  exact hcross w r R hr hrR hann t ht z hz hcl U hU hgeo.2.2.1 hgeo.2.2.2.2

end HarmonicBalls
