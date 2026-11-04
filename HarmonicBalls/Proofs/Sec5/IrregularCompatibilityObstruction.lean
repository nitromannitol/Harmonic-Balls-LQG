import HarmonicBalls.Proofs.Sec5.IrregularLeastSupersolution

/-!
# Irregular boundary obstruction to admissible comparison

At a boundary point with positive Green limit superior, an admissible least
supersolution makes the general-domain cluster accumulate at that point.
Consequently it cannot agree with a disc cluster whose closure is contained in
the domain. The existence of such a boundary point is a separate question.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- A positive Green limit at the boundary prevents an admissible general-domain
cluster from agreeing even in closure with a compactly contained set. -/
theorem closure_clusterOn_ne_of_frequently_green_pos
    {μ : Measure ℂ} {U : Set ℂ} {z y : ℂ} {t c : ℝ} {A : Set ℂ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hA : closure A ⊆ U) :
    closure (clusterOn μ U z t) ≠ closure A := by
  intro heq
  have hycl := boundary_mem_closure_clusterOn_of_frequently_green_pos hz hy hyU ht hc hv hG
  exact hyU (hA (heq ▸ hycl))

/-- In the disc-compact branch of general-domain compatibility, equality
forces the general-domain least supersolution to be inadmissible at any
boundary point with positive Green limit superior. -/
theorem not_mem_supersolutionsOn_of_disc_compact_compatibility
    {μ : Measure ℂ} {U : Set ℂ} {r t c : ℝ} {z y : ℂ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x)
    (hcl : closure (cluster μ r z t) ⊆ U)
    (heq : cluster μ r z t = clusterOn μ U z t) :
    leastSupersolutionOn μ U z t ∉ supersolutionsOn μ U z t := by
  intro hv
  apply closure_clusterOn_ne_of_frequently_green_pos hz hy hyU ht hc hG hv hcl
  exact (congrArg closure heq).symm

/-- The same obstruction applies to the compact regularized-family branch of
strong compatibility, without any assumption on cluster openness. -/
theorem not_mem_supersolutionsOn_of_regularized_compact_compatibility
    {μ : Measure ℂ} {U A : Set ℂ} {z y : ℂ} {t c : ℝ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x)
    (hcl : closure A ⊆ U) (heq : closure A = closure (clusterOn μ U z t)) :
    leastSupersolutionOn μ U z t ∉ supersolutionsOn μ U z t := by
  intro hv
  exact closure_clusterOn_ne_of_frequently_green_pos hz hy hyU ht hc hG hv hcl heq.symm

end HarmonicBalls
