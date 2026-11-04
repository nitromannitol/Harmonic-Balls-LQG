import HarmonicBalls.Proofs.Sec5.CompactStrongCompatibility

/-! # Least supersolutions at irregular boundary points -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- Zero is a general-domain supersolution at nonnegative times. -/
theorem zero_mem_supersolutionsOn {μ : Measure ℂ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    (0 : ℂ → ℝ) ∈ supersolutionsOn μ U z t :=
  ⟨continuous_zero.continuousOn, laplacianLE_zero μ _, fun x _ _ => by
    simpa using mul_nonneg ht (greenFunction_nonneg hUb z x)⟩

/-- The least supersolution is zero at any boundary point distinct from the pole. -/
theorem leastSupersolutionOn_eq_zero_of_boundary {μ : Measure ℂ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) {z y : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hy : y ∈ closure U) (hyU : y ∉ U) (hyz : y ≠ z) :
    leastSupersolutionOn μ U z t y = 0 := by
  apply le_antisymm
  · exact leastSupersolutionOn_le_of_mem (zero_mem_supersolutionsOn hUb ht) hy hyz
  · have h := le_csInf (((show (supersolutionsOn μ U z t).Nonempty from
        ⟨0, zero_mem_supersolutionsOn hUb ht⟩)).image (fun w : ℂ → ℝ => w y))
        (show ∀ a ∈ (fun w : ℂ → ℝ => w y) '' supersolutionsOn μ U z t,
          -t * greenFunction U z y ≤ a from by
            rintro _ ⟨w, hw, rfl⟩
            exact hw.2.2 y hy hyz)
    simpa [leastSupersolutionOn, greenFunction_of_notMem_right hyU] using h

/-- At a boundary point with a positive Green limit superior, continuity of
the least supersolution forces the cluster to accumulate at the boundary. -/
theorem boundary_mem_closure_clusterOn_of_continuousWithinAt
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z y : ℂ} {t c : ℝ} (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hcont : ContinuousWithinAt (leastSupersolutionOn μ U z t) U y)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x) :
    y ∈ closure (clusterOn μ U z t) := by
  have hyz : y ≠ z := fun h => hyU (h ▸ hz)
  have hvy := leastSupersolutionOn_eq_zero_of_boundary (μ := μ) hUb (le_of_lt ht) hy hyU hyz
  have hlt : -(t * c) < leastSupersolutionOn μ U z t y := by
    rw [hvy]
    have := mul_pos ht hc
    linarith
  have hnear : ∀ᶠ x in 𝓝[U] y, -(t * c) < leastSupersolutionOn μ U z t x :=
    hcont.eventually (Ioi_mem_nhds hlt)
  have hfreq : ∃ᶠ x in 𝓝[U] y, x ∈ clusterOn μ U z t := by
    apply (hG.and_eventually (hnear.and self_mem_nhdsWithin)).mono
    intro x ⟨hxG, hxv, hxU⟩
    refine ⟨hxU, Or.inr ?_⟩
    nlinarith
  exact mem_closure_of_frequently_of_tendsto hfreq nhdsWithin_le_nhds

/-- If the cluster is compactly contained, a positive Green limit superior
forces the least supersolution to be discontinuous at that boundary point. -/
theorem not_continuousWithinAt_leastSupersolutionOn_of_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z y : ℂ} {t c : ℝ} (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    ¬ ContinuousWithinAt (leastSupersolutionOn μ U z t) U y := by
  intro hcont
  exact hyU (hcl (boundary_mem_closure_clusterOn_of_continuousWithinAt
    hUb hz hy hyU ht hc hcont hG))

/-- The compact-regularized-family branch of strong compatibility forces
boundary discontinuity of the least supersolution at a positive Green limit. -/
theorem not_continuousWithinAt_of_strong_compatibility_at_boundary
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z y : ℂ} {t c : ℝ} {A : Set ℂ}
    (hz : z ∈ U) (hy : y ∈ closure U) (hyU : y ∉ U)
    (ht : 0 < t) (hc : 0 < c)
    (hG : ∃ᶠ x in 𝓝[U] y, c ≤ greenFunction U z x)
    (hA : closure A ⊆ U) (heq : closure A = closure (clusterOn μ U z t)) :
    ¬ ContinuousWithinAt (leastSupersolutionOn μ U z t) U y := by
  apply not_continuousWithinAt_leastSupersolutionOn_of_compact_containment
    hUb hz hy hyU ht hc hG
  rw [← heq]
  exact hA

end HarmonicBalls
