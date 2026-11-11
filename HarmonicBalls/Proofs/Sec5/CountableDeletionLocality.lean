import HarmonicBalls.Proofs.Sec5.CompactFamilyMeasureLocality

/-! # Locality after deleting countably many points -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A countable set in a disc is null for a measure with volume growth there. -/
theorem VolumeGrowth.measure_countable {μ : Measure ℂ} {R βm βp : ℝ}
    (hV : VolumeGrowth μ R βm βp) {K : Set ℂ} (hK : K.Countable)
    (hsub : K ⊆ ball (0 : ℂ) R) : μ K = 0 := by
  rw [← biUnion_of_singleton K, measure_biUnion_null_iff hK]
  exact fun x hx => hV.measure_singleton (hsub hx)

/-- Volume growth on all scales makes every countable set null. -/
theorem measure_countable_of_volumeGrowth_allScales {μ : Measure ℂ} {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {K : Set ℂ} (hK : K.Countable) : μ K = 0 := by
  rw [← biUnion_of_singleton K, measure_biUnion_null_iff hK]
  intro x hx
  let r : ℝ := ‖x‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  apply (hV r hr).measure_singleton
  simp only [mem_ball, dist_zero_right]
  dsimp [r]
  linarith

/-- Agreement away from a common null set implies agreement on the whole set. -/
theorem restrict_eq_of_restrict_sdiff_eq_of_null {μ ν : Measure ℂ} {U K : Set ℂ}
    (hμK : μ K = 0) (hνK : ν K = 0)
    (h : μ.restrict (U \ K) = ν.restrict (U \ K)) :
    μ.restrict U = ν.restrict U := by
  calc
    μ.restrict U = μ.restrict (U \ K) := (Measure.restrict_congr_set (sdiff_null_ae_eq_self hμK)).symm
    _ = ν.restrict (U \ K) := h
    _ = ν.restrict U := Measure.restrict_congr_set (sdiff_null_ae_eq_self hνK)

/-- If measures agree on a disc away from a countable set contained in that
  disc, all of their disc clusters agree, at every centre and time. -/
theorem cluster_eq_of_restrict_sdiff_countable
    {μ ν : Measure ℂ} {R βm βp βm' βp' : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R βm' βp')
    {K : Set ℂ} (hK : K.Countable) (hsub : K ⊆ ball (0 : ℂ) R)
    (hμν : μ.restrict (ball (0 : ℂ) R \ K) = ν.restrict (ball (0 : ℂ) R \ K))
    (z : ℂ) (t : ℝ) : cluster μ R z t = cluster ν R z t := by
  have h := clusterOn_eq_of_restrict_eq measurableSet_ball
    (restrict_eq_of_restrict_sdiff_eq_of_null (hVμ.measure_countable hK hsub)
      (hVν.measure_countable hK hsub) hμν) z t
  simpa only [clusterOn_ball μ hR.ne', clusterOn_ball ν hR.ne'] using h

/-- Removing a countable set of points from the region on which two measures
agree does not affect a regularized cluster compactly contained in the
original region. The deleted points may lie in the cluster. -/
theorem regularizedFamily_eq_of_restrict_sdiff_countable
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hK : K.Countable)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t := by
  have hμK : μ K = 0 := measure_countable_of_volumeGrowth_allScales hVμ hK
  have hνK : ν K = 0 := measure_countable_of_volumeGrowth_allScales hVν hK
  exact regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
    (restrict_eq_of_restrict_sdiff_eq_of_null hμK hνK hμν) ht hΛ hΛ' hcl

/-- Local agreement of approximating fields off a closed countable set
suffices for equality of compactly contained regularized clusters. -/
theorem IsLQGLimit.regularizedFamily_eq_of_countable_deletion
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} (hU : IsOpen U) (hKc : IsClosed K) (hK : K.Countable)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ C, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_sdiff_countable hμ hν hVμ hVν hU hK
    (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc) ht hΛ hΛ' hcl


end HarmonicBalls
