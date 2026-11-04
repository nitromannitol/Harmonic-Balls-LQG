import HarmonicBalls.Proofs.Sec5.IrregularBoundaryContact
import HarmonicBalls.Proofs.Sec5.GeneralDomainDiscLocality

/-! # Compatibility when the general-domain cluster is compactly contained -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace
open scoped Topology

/-- A Green function which vanishes at the boundary has a Green difference
which extends harmonically through the pole and continuously to the closure. -/
theorem exists_continuousOn_green_difference_of_boundary_limits
    {U : Set ℂ} (hU : IsOpen U) {r : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    ∃ h : ℂ → ℝ, ContinuousOn h (closure U) ∧ HarmonicOnNhd h U ∧
      ∀ x ∈ closure U, x ≠ z →
        greenFunction U z x - greenFunction (ball 0 r) z x = h x := by
  classical
  obtain ⟨h₀, hh₀, hG⟩ := exists_harmonicOnNhd_greenFunction_difference hU
    (isBounded_ball.subset hsub) hsub hz
  let h : ℂ → ℝ := fun x => if x ∈ U then h₀ x else -greenFunction (ball 0 r) z x
  have hinside : ∀ x ∈ U, h x = h₀ x := by intro x hx; simp [h, hx]
  have houtside : ∀ x ∉ U, h x = -greenFunction (ball 0 r) z x := by
    intro x hx; simp [h, hx]
  have hh : HarmonicOnNhd h U := by
    intro x hx
    apply (harmonicAt_congr_nhds ?_).2 (hh₀ x hx)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hinside y hy
  have hcont : ContinuousOn h (closure U) := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact (hh.continuousOn.continuousAt (hU.mem_nhds hyU)).continuousWithinAt
    · have hyz : y ≠ z := fun e => hyU (e ▸ hz)
      have hGR : ContinuousAt (greenFunction (ball 0 r) z) y :=
        (continuousOn_greenFunction_ball (hsub hz)).continuousAt
          (isOpen_compl_singleton.mem_nhds hyz)
      have hlim := (hboundary y hy hyU).sub hGR.continuousWithinAt
      have hne : ∀ᶠ x in 𝓝[U] y, x ≠ z :=
        (show ∀ᶠ x in 𝓝 y, x ≠ z from isOpen_compl_singleton.mem_nhds hyz).filter_mono
          nhdsWithin_le_nhds
      have hev : h =ᶠ[𝓝[U] y] fun x =>
          greenFunction U z x - greenFunction (ball 0 r) z x := by
        filter_upwards [self_mem_nhdsWithin, hne] with x hx hxz
        rw [hinside x hx, ← hG x hx hxz]
      have hin : ContinuousWithinAt h U y := by
        change Tendsto h (𝓝[U] y) (𝓝 (h y))
        simpa [houtside y hyU] using hlim.congr' hev.symm
      have hout : ContinuousWithinAt h Uᶜ y := by
        change Tendsto h (𝓝[Uᶜ] y) (𝓝 (h y))
        have hneg : Tendsto (fun x => -greenFunction (ball 0 r) z x)
            (𝓝[Uᶜ] y) (𝓝 (-greenFunction (ball 0 r) z y)) := hGR.neg.continuousWithinAt
        have heq : (fun x => -greenFunction (ball 0 r) z x) =ᶠ[𝓝[Uᶜ] y] h := by
          filter_upwards [self_mem_nhdsWithin] with x hx
          exact (houtside x hx).symm
        simpa [houtside y hyU] using hneg.congr' heq
      have ha : ContinuousAt h y := by
        simpa only [union_compl_self, continuousWithinAt_univ] using hin.union hout
      exact ha.continuousWithinAt
  refine ⟨h, hcont, hh, ?_⟩
  intro x hx hxz
  by_cases hxU : x ∈ U
  · rw [hinside x hxU]
    exact hG x hxU hxz
  · rw [houtside x hxU, greenFunction_of_notMem_right hxU]
    ring

/-- If the general-domain cluster is compactly contained and its least
supersolution is admissible, it agrees with the enclosing-disc cluster. -/
theorem clusterOn_eq_cluster_of_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U) (ht : 0 < t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    clusterOn μ U z t = cluster μ r z t := by
  have hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
    intro y hy hyU
    exact tendsto_greenFunction_zero_of_clusterOn_compact_containment
      (isBounded_ball.subset hsub) hz hy hyU ht hv hcl
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hsub hz hboundary
  exact clusterOn_eq_cluster_of_green_difference_of_nonneg hU hsub hz (le_of_lt ht)
    hv hc hh hG (Or.inr hcl)

/-- Under compact containment of the general-domain cluster, equality of two
measures on the domain implies equality of their enclosing-disc clusters. -/
theorem cluster_eq_of_restrict_eq_of_clusterOn_compact_containment
    {μ ν : Measure ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hμν : μ.restrict U = ν.restrict U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U) (ht : 0 < t)
    (hvμ : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    cluster μ r z t = cluster ν r z t := by
  have hlocal := clusterOn_eq_of_restrict_eq hU.measurableSet hμν z t
  have hsuper := supersolutionsOn_eq_of_restrict_eq hU.measurableSet hμν z t
  have hvν : leastSupersolutionOn ν U z t ∈ supersolutionsOn ν U z t := by
    have hvEq : leastSupersolutionOn μ U z t = leastSupersolutionOn ν U z t := by
      funext x
      unfold leastSupersolutionOn
      rw [hsuper]
    rw [← hvEq, ← hsuper]
    exact hvμ
  have hclν : closure (clusterOn ν U z t) ⊆ U := by
    rw [← hlocal]
    exact hcl
  have heqμ := clusterOn_eq_cluster_of_compact_containment hU hsub hz ht hvμ hcl
  have heqν := clusterOn_eq_cluster_of_compact_containment hU hsub hz ht hvν hclν
  exact heqμ.symm.trans (hlocal.trans heqν)

end HarmonicBalls
