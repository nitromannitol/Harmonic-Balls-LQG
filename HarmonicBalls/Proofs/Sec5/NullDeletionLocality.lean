import HarmonicBalls.Proofs.Sec5.CountableDeletionLocality

/-! # Locality after deletion of a common null set

The deleted set need not be countable or disjoint from the cluster. These
results concern locality of disc and regularized clusters; they do not assert
compatibility with the obstacle problem on the deleted domain.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Agreement off a common null set determines all clusters in a disc. -/
theorem cluster_eq_of_restrict_sdiff_null
    {μ ν : Measure ℂ} {R : ℝ} (hR : 0 < R) {K : Set ℂ}
    (hμK : μ K = 0) (hνK : ν K = 0)
    (hμν : μ.restrict (ball (0 : ℂ) R \ K) = ν.restrict (ball (0 : ℂ) R \ K))
    (z : ℂ) (t : ℝ) : cluster μ R z t = cluster ν R z t := by
  have h := clusterOn_eq_of_restrict_eq measurableSet_ball
    (restrict_eq_of_restrict_sdiff_eq_of_null hμK hνK hμν) z t
  simpa only [clusterOn_ball μ hR.ne', clusterOn_ball ν hR.ne'] using h

/-- Agreement off a common null set determines a regularized cluster whenever
its closure is contained in the original open set. -/
theorem regularizedFamily_eq_of_restrict_sdiff_null
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hμK : μ K = 0) (hνK : ν K = 0)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
    (restrict_eq_of_restrict_sdiff_eq_of_null hμK hνK hμν) ht hΛ hΛ' hcl

/-- Local agreement of the approximating fields away from a closed common
null set determines a compactly contained regularized cluster. -/
theorem IsLQGLimit.regularizedFamily_eq_of_null_deletion
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hKc : IsClosed K)
    (hμK : μ K = 0) (hνK : ν K = 0)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ C, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_sdiff_null hμ hν hVμ hVν hU hμK hνK
    (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc) ht hΛ hΛ' hcl

#print axioms cluster_eq_of_restrict_sdiff_null
#print axioms regularizedFamily_eq_of_restrict_sdiff_null
#print axioms IsLQGLimit.regularizedFamily_eq_of_null_deletion

end HarmonicBalls
