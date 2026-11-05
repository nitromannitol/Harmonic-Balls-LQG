import HarmonicBalls.Proofs.Sec5.CountableDeletionLocality

/-! # Locality outside a relatively countable set

Agreement off a relatively countable set determines the measure on the whole
region when both measures have volume growth. The exceptional points may lie
in the cluster, including at its centre.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Agreement away from a relatively countable set determines the measures
on the entire region. -/
theorem restrict_eq_of_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K)) :
    μ.restrict U = ν.restrict U := by
  have hset : U \ (K ∩ U) = U \ K := by ext x; simp
  apply restrict_eq_of_restrict_sdiff_eq_of_null
    (measure_countable_of_volumeGrowth_allScales hVμ hK)
    (measure_countable_of_volumeGrowth_allScales hVν hK)
  simpa only [hset] using hμν

/-- Agreement off a relatively countable set determines a regularized
cluster compactly contained in the region, even when it contains deleted points. -/
theorem regularizedFamily_eq_of_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (Λ' t) ⊆ U) : Λ t = Λ' t := by
  have heq := restrict_eq_of_restrict_sdiff_relative_countable hVμ hVν hK hμν
  rcases hcl with hcl | hcl
  · exact regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU heq
      ht hΛ hΛ' hcl
  · exact (regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hν hμ hVν hVμ hU heq.symm
      ht hΛ' hΛ hcl).symm

/-- Local agreement of circle averages away from a relatively countable set
identifies regularized clusters compactly contained in the original region. -/
theorem IsLQGLimit.regularizedFamily_eq_of_relative_countable_measure_locality
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U ∨ closure (Λ' t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_sdiff_relative_countable hμ hν hVμ hVν hU hK
    (hμlim.restrict_eq hνlim hD hloc) ht hΛ hΛ' hcl

/-- Under the same local agreement, compact containment in the original
region is equivalent for the two regularized families. -/
theorem regularizedFamily_containment_iff_of_restrict_sdiff_relative_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hK : (K ∩ U).Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z) :
    closure (Λ t) ⊆ U ↔ closure (Λ' t) ⊆ U := by
  constructor
  · intro hcl
    rw [← regularizedFamily_eq_of_restrict_sdiff_relative_countable hμ hν hVμ hVν
      hU hK hμν ht hΛ hΛ' (Or.inl hcl)]
    exact hcl
  · intro hcl
    rw [regularizedFamily_eq_of_restrict_sdiff_relative_countable hμ hν hVμ hVν
      hU hK hμν ht hΛ hΛ' (Or.inr hcl)]
    exact hcl

/-- Circle-average agreement off the relatively countable set identifies
the original region's compact-containment event. -/
theorem IsLQGLimit.regularizedFamily_containment_iff_of_relative_countable
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z) :
    closure (Λ t) ⊆ U ↔ closure (Λ' t) ⊆ U :=
  regularizedFamily_containment_iff_of_restrict_sdiff_relative_countable hμ hν hVμ hVν
    hU hK (hμlim.restrict_eq hνlim hD hloc) ht hΛ hΛ'

#print axioms regularizedFamily_containment_iff_of_restrict_sdiff_relative_countable
#print axioms IsLQGLimit.regularizedFamily_containment_iff_of_relative_countable
#print axioms restrict_eq_of_restrict_sdiff_relative_countable
#print axioms regularizedFamily_eq_of_restrict_sdiff_relative_countable
#print axioms IsLQGLimit.regularizedFamily_eq_of_relative_countable_measure_locality

end HarmonicBalls
