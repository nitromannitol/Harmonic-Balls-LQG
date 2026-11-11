import HarmonicBalls.Proofs.Sec5.LocalRankHarmonicExtension
import HarmonicBalls.Proofs.Sec5.CompactStrongCompatibility
import HarmonicBalls.Proofs.Sec5.CompactFamilyMeasureLocality

/-! # Compact-containment locality after locally finite-rank deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A compactly contained punctured-domain cluster determines the regularized
family, without requiring admissibility of the punctured-domain infimum. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hc := closure_clusterOn_sdiff_of_local_rank hμ hU hUb hUR hKc hK
    hqc hq ht.le hz hw hopenU
  have hfull : closure (clusterOn μ U z t) ⊆ U := by
    rw [← hc]
    exact hcl.trans sdiff_subset
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]; linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have heq := hΛ.2.2 t ht r hr hΛr r le_rfl
  rw [hc, heq, closure_regularizedCluster_eq_of_isOpen (hopen r hr (hUr hz.1)),
    ← clusterOn_eq_cluster_of_compact_containment hU hUr hz.1 ht hw hfull]

/-- If the full-domain Green function tends to zero at its boundary, the
regularized-family containment alternative also gives closure compatibility. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_green_boundary
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have hc := closure_clusterOn_sdiff_of_local_rank hμ hU hUb hUR hKc hK
    hqc hq ht.le hz hw hopenU
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by
    have h := le_max_left (1 : ℝ) (max r₁ r₂)
    dsimp [r]; linarith
  have hr₁r : r₁ ≤ r := by
    have h := (le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hr₂r : r₂ ≤ r := by
    have h := (le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))
    dsimp [r]; linarith
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen (hopen r hr (hUr hz.1))]
  obtain ⟨h, hcont, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hUr hz.1 hboundary
  have heq := clusterOn_eq_cluster_of_green_difference_of_nonneg hU hUr hz.1 ht.le
    hw hcont hh hG (Or.inl (hcluster ▸ hcl.trans sdiff_subset))
  rw [hc, heq, ← hcluster]

/-- Both compact-containment alternatives give closure compatibility when
the full-domain Green function vanishes at the boundary. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  rcases hcl with hcl | hcl
  · exact regularizedFamily_closure_eq_clusterOn_sdiff_of_green_boundary
      hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hboundary hΛ hopen hcl
  · exact regularizedFamily_closure_eq_clusterOn_sdiff_of_local_rank
      hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hΛ hopen hcl

/-- Agreement of measures on a punctured domain identifies regularized
families when the first punctured-domain cluster is compactly contained. -/
theorem regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
    intro r hr hzr
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hVμ r hr) z hzr t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr (hVμ r hr) hzr ht
  have heq := regularizedFamily_closure_eq_clusterOn_sdiff_of_local_rank
    hμ hU hUb hUR hKc hK hqc hq ht hz hw hopenU hΛ hopen hcl
  apply regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν
    (hU.sdiff hKc) hμν ht hΛ hΛ'
  rw [heq]
  exact hcl

/-- Local agreement of circle-average approximations on the punctured domain
implies the same compact-containment locality for their limiting measures. -/
theorem IsLQGLimit.regularizedFamily_eq_of_sdiff_local_rank
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ C, hε (dyadicScale k) y = hε' (dyadicScale k) y)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank hμ hν hVμ hVν hU hUb hUR
    hKc hK (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc)
    hqc hq ht hz hw hopenU hΛ hΛ' hcl

/-- Either compact-containment alternative gives measure locality after a
closed deletion of locally finite rank in the original domain. -/
theorem regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank_or
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  rcases hcl with hcl | hcl
  · exact regularizedFamily_eq_of_restrict_eq_of_volumeGrowth hμ hν hVμ hVν
      (hU.sdiff hKc) hμν ht hΛ hΛ' hcl
  · exact regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank hμ hν hVμ hVν
      hU hUb hUR hKc hK hμν hqc hq ht hz hw hopenU hΛ hΛ' hcl

/-- Local agreement of circle averages implies locality under either
compact-containment alternative. -/
theorem IsLQGLimit.regularizedFamily_eq_of_sdiff_local_rank_or
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn U K)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ K →
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ C, hε (dyadicScale k) y = hε' (dyadicScale k) y)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank_or hμ hν hVμ hVν hU hUb hUR
    hKc hK (hμlim.restrict_eq hνlim (hU.sdiff hKc) hloc)
    hqc hq ht hz hw hopenU hΛ hΛ' hcl

end HarmonicBalls
