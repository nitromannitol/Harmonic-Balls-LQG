import HarmonicBalls.Proofs.Sec5.ExhaustionClusterCompatibility

/-! # Comparison of nested Green-regular domains

The Green and obstacle arguments use the potential-theoretic infrastructure of
Leonardo Bonanno. The boundary limits are explicit: no regularity is asserted
for an arbitrary open set.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Compact containment of the larger cluster in the smaller domain gives
exact equality of the clusters and of their off-pole odometers. -/
theorem nested_greenRegular_cluster_and_odometer_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hvol : VolumeGrowth μ R βm βp)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (hVR : V ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hUreg : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    (hVreg : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    (hcl : closure (clusterOn μ V z t) ⊆ U) :
    clusterOn μ U z t = clusterOn μ V z t ∧
      ∀ x ∈ U, x ≠ z →
        leastSupersolutionOn μ U z t x + t * greenFunction U z x =
          leastSupersolutionOn μ V z t x + t * greenFunction V z x := by
  have hzV : z ∈ V := hUV hz
  have hUR : U ⊆ ball (0 : ℂ) R := hUV.trans hVR
  have hv := leastSupersolutionOn_mem_of_greenRegular hμ hR hvol hV hVR hzV ht hVreg
  have hvdisc : clusterOn μ V z t = cluster μ R z t :=
    clusterOn_eq_cluster_of_compact_containment hV hVR hzV ht hv (hcl.trans hUV)
  have hdisc : closure (cluster μ R z t) ⊆ U := by
    rw [← hvdisc]
    exact hcl
  have hu := leastSupersolutionOn_mem_of_greenRegular hμ hR hvol hU hUR hz ht hUreg
  have hmono := clusterOn_subset_of_nested_regular (μ := μ) hU hV
    (isBounded_ball.subset hVR) hUV hz ht.le hUreg hVreg
  have hucl : closure (clusterOn μ U z t) ⊆ U := (closure_mono hmono).trans hcl
  have hudisc := clusterOn_eq_cluster_of_compact_containment hU hUR hz ht hu hucl
  refine ⟨hudisc.trans hvdisc.symm, ?_⟩
  intro x hx hxz
  have heU := odometerOn_eq_disc_of_compact_disc_cluster hμ hU hR hvol hUR hz hx hxz ht hUreg hdisc
  have heV := odometerOn_eq_disc_of_compact_disc_cluster hμ hV hR hvol hVR hzV (hUV hx) hxz ht hVreg
    (hdisc.trans hUV)
  exact heU.trans heV.symm

#print axioms nested_greenRegular_cluster_and_odometer_eq

end HarmonicBalls
