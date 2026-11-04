import HarmonicBalls.Proofs.Sec5.CompactClusterMeasureLocality
import HarmonicBalls.Steps.Sec5.StrongCompatibility

/-! # Locality of compactly contained regularized cluster families

Disc compatibility transfers locality of compactly contained disc clusters
to regularized cluster families without using the obstacle on the open set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Two regularized cluster families agree at a positive time when their
measures agree on an open set containing the closure of the first family. -/
theorem regularizedFamily_eq_of_restrict_eq_of_closure_subset
    {μ ν : Measure ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hμν : μ.restrict U = ν.restrict U) {z : ℂ} {t : ℝ} (ht : 0 < t)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hvμ : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r →
      leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hvν : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r →
      leastSupersolution ν r z t ∈ supersolutions ν r z t)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t := by
  obtain ⟨r₁, hr₁⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ'.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have := le_max_left (1 : ℝ) (max r₁ r₂)
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
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛ'r : closure (Λ' t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hz : z ∈ ball (0 : ℂ) r := hΛr (subset_closure (hΛ.1.mem t ht))
  have hleft := hΛ.2.2 t ht r hr hΛr r le_rfl
  have hright := hΛ'.2.2 t ht r hr hΛ'r r le_rfl
  have hclosure : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hleft, closure_regularizedCluster_eq_of_isOpen (hopen r hr hz)]
  have hclusters := cluster_eq_of_restrict_eq_of_closure_subset_inter hU hμν hz
    (hvμ r hr hz) (hvν r hr hz) (hclosure ▸ hcl) (hclosure ▸ hΛr)
  rw [hleft, hright, regularizedCluster, regularizedCluster, hclusters]

/-- Local finiteness and volume growth at every radius give locality of a
compactly contained regularized cluster family. -/
theorem regularizedFamily_eq_of_restrict_eq_of_volumeGrowth
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U : Set ℂ} (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t := by
  apply regularizedFamily_eq_of_restrict_eq_of_closure_subset hU hμν ht hΛ hΛ'
  · intro r hr hz
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hVμ r hr) z hz t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hr
      (hVμ r hr) hz ht
  · intro r hr hz
    exact (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hr (hVμ r hr) hz ht).2.2
  · intro r hr hz
    exact (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hν hr (hVν r hr) hz ht).2.2
  · exact hcl

/-- Locally equal circle averages yield the same compactly contained
regularized cluster when both limiting measures have volume growth. -/
theorem IsLQGLimit.regularizedFamily_eq_of_compact_containment
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {z : ℂ} {t : ℝ} (ht : 0 < t) {Λ Λ' : ℝ → Set ℂ}
    (hΛ : IsRegularizedClusterFamily μ Λ z) (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν hU
    (hμlim.restrict_eq hνlim hU hloc) ht hΛ hΛ' hcl

end HarmonicBalls
