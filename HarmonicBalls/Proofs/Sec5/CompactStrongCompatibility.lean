import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility
import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Strong compatibility from compact general-domain clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The compact-general-domain branch of strong compatibility for a
regularized cluster family. The admissibility assumption is explicit. -/
theorem regularizedFamily_closure_eq_clusterOn_of_compact_containment
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) {Λ : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]
    linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]
    linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have heq := hΛ.2.2 t ht r hr hΛr r le_rfl
  rw [heq, closure_regularizedCluster_eq_of_isOpen (hopen r hr),
    ← clusterOn_eq_cluster_of_compact_containment hU hUr hz ht hv hcl]

/-- Compactly contained general-domain clusters determine regularized cluster
families locally: agreement of measures on the domain gives equal sets. -/
theorem regularizedFamily_eq_of_restrict_eq_of_clusterOn_compact_containment
    {μ ν : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hμν : μ.restrict U = ν.restrict U) {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hopenμ : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hopenν : ∀ r : ℝ, 0 < r → IsOpen (cluster ν r z t))
    (hvμ : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    Λ t = Λ' t := by
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
  have hleft := regularizedFamily_closure_eq_clusterOn_of_compact_containment
    hU hUb hz ht hΛ hopenμ hvμ hcl
  have hright := regularizedFamily_closure_eq_clusterOn_of_compact_containment
    hU hUb hz ht hΛ' hopenν hvν hclν
  have hclosures : closure (Λ t) = closure (Λ' t) :=
    hleft.trans ((congrArg closure hlocal).trans hright.symm)
  calc
    Λ t = interior (closure (Λ t)) := (hΛ.1.isRegularOpen t ht).symm
    _ = interior (closure (Λ' t)) := congrArg interior hclosures
    _ = Λ' t := hΛ'.1.isRegularOpen t ht

/-- In particular, regularized cluster families agree when their circle-average
approximations agree locally at all sufficiently small dyadic scales. -/
theorem IsLQGLimit.regularizedFamily_eq_of_clusterOn_compact_containment
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hopenμ : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hopenν : ∀ r : ℝ, 0 < r → IsOpen (cluster ν r z t))
    (hvμ : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_clusterOn_compact_containment hU hUb
    (hμlim.restrict_eq hνlim hU hloc) hz ht hΛ hΛ' hopenμ hopenν hvμ hcl

end HarmonicBalls
