import HarmonicBalls.Proofs.Sec10.ComplementaryHoleCrossing
import HarmonicBalls.Proofs.Sec10.ComplementComponents

/-!
# Crossing containment forces a connected complement

For a nonempty set compactly contained in the unit disk, the crossing
containment in Lemma 10.5 forces its entire closed-set complement to have
only one component. This implication does not assert that LQG clusters have
or lack holes.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- If a component satisfies the crossing-containment conclusion, then it is
the whole complement of the closure. -/
theorem compl_closure_eq_of_crossing_containment
    {G U : Set ℂ} (hGne : G.Nonempty) (hGdisk : closure G ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn (closure G)ᶜ)
    (hcontain : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      closure (annulus w r R) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R,
        ∃ C' ∈ crossingComponents (G ∩ annulus w r R) w r R, C' ⊆ C) :
    (closure G)ᶜ = U := by
  classical
  obtain ⟨p, hp, rfl⟩ := hU
  let K := closure G
  let U := connectedComponentIn Kᶜ p
  have hKne : K.Nonempty := hGne.mono subset_closure
  have hUsub : U ⊆ Kᶜ := connectedComponentIn_subset _ _
  apply Subset.antisymm
  · intro y hy
    by_contra hyU
    let V := connectedComponentIn Kᶜ y
    have hyV : y ∈ V := mem_connectedComponentIn hy
    have hVopen : IsOpen V := isClosed_closure.isOpen_compl.connectedComponentIn
    have hVsub : V ⊆ Kᶜ := connectedComponentIn_subset _ _
    have hGV : Disjoint G V := by
      rw [disjoint_left]
      intro x hxG hxV
      exact hVsub hxV (subset_closure hxG)
    have hUV : Disjoint U V := by
      rw [disjoint_left]
      intro x hxU hxV
      have hEq : U = V := (connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm
      rw [← hEq] at hyV
      exact hyU hyV
    obtain ⟨x, hxV, hxK⟩ := closure_component_compl_inter_nonempty
      (K := K) isClosed_closure hKne hy
    have hxball : x ∈ ball (0 : ℂ) 1 := hGdisk hxK
    obtain ⟨q, hqball, hqV⟩ := mem_closure_iff.mp hxV _ isOpen_ball hxball
    exact crossing_containment_forbids_complementary_open_hole hGV hUV hVopen hcontain
      ⟨q, hqV, hqball⟩
  · exact hUsub

/-- In particular, crossing containment for one complementary component
forces the entire complement to be connected. -/
theorem isConnected_compl_closure_of_crossing_containment
    {G U : Set ℂ} (hGne : G.Nonempty) (hGdisk : closure G ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn (closure G)ᶜ)
    (hcontain : ∀ (w : ℂ) (r R : ℝ), 0 < r → r < R →
      closure (annulus w r R) ⊆ ball 0 1 →
      ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R,
        ∃ C' ∈ crossingComponents (G ∩ annulus w r R) w r R, C' ⊆ C) :
    IsConnected (closure G)ᶜ := by
  have heq := compl_closure_eq_of_crossing_containment hGne hGdisk hU hcontain
  obtain ⟨p, hp, rfl⟩ := hU
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hp

/-- Lemma 10.5, together with cluster geometry from volume growth, implies
that every compactly contained cluster has connected closed-set complement.
The premise is the frozen Lemma 10.5 statement, kept explicit. -/
theorem ae_cluster_compl_closure_connected_of_crossing_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      IsConnected (closure (cluster (μ ω) 1 z t))ᶜ := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h5 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2] with ω hcross hgeom
  intro t ht z hz hcl
  let G := cluster (μ ω) 1 z t
  have hGne : G.Nonempty := ⟨z, self_mem_cluster hz⟩
  have htwo : (2 : ℂ) ∈ (closure G)ᶜ := by
    intro h
    have hball := hcl h
    have hdist : dist (2 : ℂ) 0 < 1 := mem_ball.mp hball
    norm_num [dist_eq_norm] at hdist
  let U := connectedComponentIn (closure G)ᶜ (2 : ℂ)
  have hU : U ∈ connectedComponentsIn (closure G)ᶜ := ⟨2, htwo, rfl⟩
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  apply isConnected_compl_closure_of_crossing_containment hGne hcl hU
  intro w r R hr hrR hann C hC
  exact hcross w r R hr hrR hann t ht z hz hcl U hU hg.2.2.1 hg.2.2.2.2 C hC

end HarmonicBalls
