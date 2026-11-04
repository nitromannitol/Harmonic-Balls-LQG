import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen

/-! # Boundary contact at a positive Green limit -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- If the Green function stays bounded away from zero arbitrarily close to a
boundary point, an admissible least supersolution forces the cluster to
accumulate at that point. -/
theorem boundary_mem_closure_clusterOn_of_frequently_green_pos
    {μ : Measure ℂ} {U : Set ℂ} {z y : ℂ} {t c : ℝ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x) :
    y ∈ closure (clusterOn μ U z t) := by
  have hyz : y ≠ z := fun h => hyU (h ▸ hz)
  have hvy : 0 ≤ leastSupersolutionOn μ U z t y := by
    have h := hv.2.2 y hy hyz
    simpa [greenFunction_of_notMem_right hyU] using h
  have hlt : -(t * c) < leastSupersolutionOn μ U z t y := by
    have := mul_pos ht hc
    linarith
  have hcont : ContinuousWithinAt (leastSupersolutionOn μ U z t) U y :=
    (hv.1 y hy).mono subset_closure
  have hnear : ∀ᶠ x in 𝓝[U] y, -(t * c) < leastSupersolutionOn μ U z t x :=
    hcont.eventually (Ioi_mem_nhds hlt)
  have hfreq : ∃ᶠ x in 𝓝[U] y, x ∈ clusterOn μ U z t := by
    apply (hG.and_eventually (hnear.and self_mem_nhdsWithin)).mono
    intro x ⟨hxG, hxv, hxU⟩
    refine ⟨hxU, Or.inr ?_⟩
    nlinarith
  exact mem_closure_of_frequently_of_tendsto hfreq nhdsWithin_le_nhds

/-- In particular, compact containment of the cluster in the domain rules out
such positive Green boundary limits whenever the least supersolution is admissible. -/
theorem not_frequently_green_pos_of_clusterOn_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} {z y : ℂ} {t c : ℝ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    ¬ ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x := by
  intro hG
  exact hyU (hcl (boundary_mem_closure_clusterOn_of_frequently_green_pos hz hy hyU ht hc hv hG))

/-- Compact containment and admissibility force the Green function to vanish
at every boundary point, in the sense of limits from within the domain. -/
theorem tendsto_greenFunction_zero_of_clusterOn_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z y : ℂ} {t : ℝ} (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun x => lt_of_lt_of_le ha (greenFunction_nonneg hUb z x))
  · intro b hb
    have h := not_frequently_green_pos_of_clusterOn_compact_containment hz hy hyU ht hb hv hcl
    exact (not_frequently.mp h).mono (fun _ hx => lt_of_not_ge hx)

end HarmonicBalls
