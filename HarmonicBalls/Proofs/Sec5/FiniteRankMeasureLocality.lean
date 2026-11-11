import HarmonicBalls.Proofs.Sec5.FiniteRankPointRemoval
import HarmonicBalls.Proofs.Sec5.CountableDeletionLocality

/-! # Measure locality outside finite-rank point sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Agreement on an open set away from a finite-rank locally finite set
implies agreement on the whole open set for measures with volume growth. -/
theorem restrict_eq_of_restrict_sdiff_finiteRank
    {μ ν : Measure ℂ} {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) {n : ℕ} (hK : LocallyFiniteRank U n K)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K)) :
    μ.restrict U = ν.restrict U := by
  have hc := countable_inter_open_of_locallyFiniteRank hU hK
  have hμ0 := measure_countable_of_volumeGrowth_allScales hVμ hc
  have hν0 := measure_countable_of_volumeGrowth_allScales hVν hc
  apply restrict_eq_of_restrict_sdiff_eq_of_null hμ0 hν0
  have hs : U \ (K ∩ U) = U \ K := by
    ext x
    simp
  simpa only [hs] using hμν

/-- Regularized clusters compactly contained in the open region are determined
by the measure away from a finite-rank locally finite set. -/
theorem regularizedFamily_eq_of_restrict_sdiff_finiteRank
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) {n : ℕ} (hK : LocallyFiniteRank U n K)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t := by
  exact regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
    (restrict_eq_of_restrict_sdiff_finiteRank hVμ hVν hU hK hμν) ht hΛ hΛ' hcl

/-- Agreement of approximating fields away from a closed finite-rank locally
finite set determines compactly contained regularized clusters. -/
theorem IsLQGLimit.regularizedFamily_eq_of_finiteRank_deletion
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hKc : IsClosed K) {n : ℕ}
    (hK : LocallyFiniteRank U n K)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ C, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_sdiff_finiteRank hμ hν hVμ hVν hU hK
    (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc) ht hΛ hΛ' hcl


end HarmonicBalls
