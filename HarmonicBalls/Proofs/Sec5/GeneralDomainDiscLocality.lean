import HarmonicBalls.Proofs.Sec5.GeneralDomainCompatibility
import HarmonicBalls.Proofs.Sec5.GeneralDomainMeasureLocality

/-!
# Locality of compactly contained disc clusters

A general-domain obstacle depends only on the measure in that domain. When
its least supersolution is admissible and the Green-function difference has a
continuous harmonic extension, general-domain compatibility transfers this
locality to a disc cluster compactly contained in the domain.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- General-domain clusters lie in enclosing disc clusters under a continuous
harmonic Green difference, without a volume-growth assumption. -/
theorem clusterOn_subset_cluster_of_green_difference_of_nonneg
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (ht : 0 ≤ t) {h : ℂ → ℝ}
    (hc : ContinuousOn h (closure U)) (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x) :
    clusterOn μ U z t ⊆ cluster μ r z t := by
  intro x hx
  refine ⟨hsub hx.1, ?_⟩
  rcases hx.2 with hxz | hxpos
  · exact Or.inl hxz
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have hle : leastSupersolutionOn μ U z t x - (-t) * h x ≤
          leastSupersolution μ r z t x := by
        apply le_csInf ((supersolutions_nonempty μ r z ht).image _)
        rintro _ ⟨w, hw, rfl⟩
        have hcomp := shifted_supersolutionOn_of_green_difference hU hsub hw hc hh hG
        have ha := leastSupersolutionOn_le_of_mem hcomp (subset_closure hx.1) hxz
        change leastSupersolutionOn μ U z t x ≤ w x + (-t) * h x at ha
        linarith
      have he := hG x (subset_closure hx.1) hxz
      have he' : t * h x = t * greenFunction U z x -
          t * greenFunction (ball 0 r) z x := by rw [← he]; ring
      linarith

/-- Compatibility under the Green-function and admissibility hypotheses holds
for every measure, without volume growth, at nonnegative times. -/
theorem clusterOn_eq_cluster_of_green_difference_of_nonneg
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U) (ht : 0 ≤ t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (cluster μ r z t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    clusterOn μ U z t = cluster μ r z t := by
  have hforward := clusterOn_subset_cluster_of_green_difference_of_nonneg
    (μ := μ) hU hsub ht hc hh hG
  have hsmall : closure (clusterOn μ U z t) ⊆ U := by
    rcases hcl with hlarge | hsmall
    · exact (closure_mono hforward).trans hlarge
    · exact hsmall
  exact Subset.antisymm hforward
    (cluster_subset_clusterOn_of_green_difference hU hsub hz hv hc hh hG hsmall)

/-- If two measures agree inside a domain, then their disc clusters agree when
the first is compactly contained in the domain, subject to the stated
general-domain obstacle and Green-function regularity hypotheses. -/
theorem cluster_eq_of_restrict_eq_of_compact_containment
    {μ ν : Measure ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    {r : ℝ}
    (hsub : U ⊆ ball (0 : ℂ) r) {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hvμ : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (cluster μ r z t) ⊆ U) :
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
  have heqμ := clusterOn_eq_cluster_of_green_difference_of_nonneg
    hU hsub hz ht hvμ hc hh hG (Or.inl hcl)
  have hsmall : closure (clusterOn ν U z t) ⊆ U := by
    rw [← hlocal, heqμ]
    exact hcl
  have hreverse := cluster_subset_clusterOn_of_green_difference hU hsub hz hvν hc hh hG hsmall
  have hforward := clusterOn_subset_cluster_of_green_difference_of_nonneg (μ := ν)
    hU hsub ht hc hh hG
  exact heqμ.symm.trans (hlocal.trans (Subset.antisymm hforward hreverse))

/-- In particular, agreement of two approximating fields on compact subsets
of the domain implies equality of the corresponding disc clusters under the
same compatibility hypotheses. -/
theorem IsLQGLimit.cluster_eq_of_compact_containment
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {r : ℝ}
    (hsub : U ⊆ ball (0 : ℂ) r) {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hvμ : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    cluster μ r z t = cluster ν r z t :=
  cluster_eq_of_restrict_eq_of_compact_containment hU
    (hμlim.restrict_eq hνlim hU hloc) hsub hz ht hvμ hc hh hG hcl

end HarmonicBalls
