import HarmonicBalls.Proofs.Sec5.LocalRankGeneralDomainLocality

/-! # Relatively closed deletions of locally finite accumulation rank -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Closing a relatively closed deletion changes it only outside the domain. -/
theorem closure_inter_eq_inter_of_isOpen_sdiff
    {U K : Set ℂ} (hD : IsOpen (U \ K)) :
    closure (U ∩ K) ∩ U = K ∩ U := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, hx.2⟩
    by_contra hxK
    have hsub : U ∩ K ⊆ (U \ K)ᶜ := by
      intro y hy hyD
      exact hyD.2 hy.2
    have hclosure := closure_minimal hsub hD.isClosed_compl
    exact hclosure hx.1 ⟨hx.2, hxK⟩
  · intro hx
    exact ⟨subset_closure ⟨hx.2, hx.1⟩, hx.2⟩

/-- Local finite accumulation rank is unchanged by closing a relatively
closed deletion outside the domain. -/
theorem locallyFiniteRankOn_closure_inter_of_isOpen_sdiff
    {U K : Set ℂ} (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K) :
    LocallyFiniteRankOn U (closure (U ∩ K)) := by
  intro C hC hCU
  obtain ⟨n, hn⟩ := hK C hC hCU
  refine ⟨n, ?_⟩
  have heq : closure (U ∩ K) ∩ C = K ∩ C := by
    ext x
    constructor
    · intro hx
      have := (Set.ext_iff.mp (closure_inter_eq_inter_of_isOpen_sdiff hD) x).mp
        ⟨hx.1, hCU hx.2⟩
      exact ⟨this.1, hx.2⟩
    · intro hx
      exact ⟨subset_closure ⟨hCU hx.2, hx.1⟩, hx.2⟩
  rw [heq]
  exact hn

/-- The domain after deletion is unchanged by taking the ambient closure of
the part of the deletion that lies in the domain. -/
theorem sdiff_closure_inter_eq_of_isOpen_sdiff
    {U K : Set ℂ} (hD : IsOpen (U \ K)) : U \ closure (U ∩ K) = U \ K := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, fun hxK => hx.2 (subset_closure ⟨hx.1, hxK⟩)⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro hxcl
    have hxK := (Set.ext_iff.mp (closure_inter_eq_inter_of_isOpen_sdiff hD) x).mp ⟨hxcl, hx.1⟩
    exact hx.2 hxK.1

/-- Green functions are unchanged by relatively closed, locally finite-rank
deletions at points remaining in the domain. -/
theorem greenFunction_sdiff_of_relative_local_rank
    {U K : Set ℂ} {R : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
    (hz : z ∈ U \ K) (hx : x ∈ U \ K) (hxz : x ≠ z) :
    greenFunction (U \ K) z x = greenFunction U z x := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hg := greenFunction_sdiff_of_local_rank hU hUR isClosed_closure
    (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK)
    (heq ▸ hz) (heq ▸ hx) hxz
  simpa only [heq] using hg

/-- A relatively closed deletion of locally finite rank removes exactly its
points from the cluster, under full-domain obstacle admissibility. -/
theorem clusterOn_sdiff_of_relative_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := clusterOn_sdiff_of_local_rank hμ hU hUb hUR isClosed_closure
    (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK) hqc hq ht (heq ▸ hz) hw
  rw [heq] at hc
  rw [hc]
  ext x
  constructor
  · rintro ⟨hx, hxK⟩
    exact ⟨hx, fun hx' => hxK (subset_closure ⟨hx.1, hx'⟩)⟩
  · rintro ⟨hx, hxK⟩
    exact ⟨hx, fun hxcl => hxK
      ((Set.ext_iff.mp (closure_inter_eq_inter_of_isOpen_sdiff hD) x).mp ⟨hxcl, hx.1⟩).1⟩

/-- Under full-cluster openness, relatively closed local-rank deletions do
not change the cluster closure. -/
theorem closure_clusterOn_sdiff_of_relative_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := closure_clusterOn_sdiff_of_local_rank hμ hU hUb hUR isClosed_closure
    (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK) hqc hq ht (heq ▸ hz) hw hopenU
  simpa only [heq] using hc

/-- Compact containment of the cluster after a relatively closed deletion
gives its closure as the closure of the regularized family. -/
theorem regularizedFamily_closure_eq_clusterOn_sdiff_of_relative_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := regularizedFamily_closure_eq_clusterOn_sdiff_of_local_rank
    hμ hU hUb hUR isClosed_closure
    (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK)
    hqc hq ht (heq ▸ hz) hw hopenU hΛ hopen (by simpa only [heq] using hcl)
  simpa only [heq] using hc

/-- Both compact-containment alternatives give closure compatibility after a
relatively closed deletion when the full-domain Green function vanishes at the boundary. -/
theorem regularizedFamily_strongCompatibility_sdiff_of_relative_local_rank
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
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
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hc := regularizedFamily_strongCompatibility_sdiff_of_local_rank
    hμ hU hUb hUR isClosed_closure
    (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK)
    hqc hq ht (heq ▸ hz) hw hopenU hboundary hΛ hopen
    (by simpa only [heq] using hcl)
  simpa only [heq] using hc

/-- Agreement of measures after a relatively closed deletion identifies
regularized families under either compact-containment alternative. -/
theorem regularizedFamily_eq_of_restrict_eq_of_relative_local_rank
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
    (hμν : μ.restrict (U \ K) = ν.restrict (U \ K))
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hz : z ∈ U \ K)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopenU : IsOpen (clusterOn μ U z t))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) : Λ t = Λ' t := by
  have heq := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  exact regularizedFamily_eq_of_restrict_eq_of_sdiff_local_rank_or hμ hν hVμ hVν
    hU hUb hUR isClosed_closure (locallyFiniteRankOn_closure_inter_of_isOpen_sdiff hD hK)
    (by simpa only [heq] using hμν) hqc hq ht (heq ▸ hz) hw hopenU hΛ hΛ'
    (by simpa only [heq] using hcl)

/-- Local agreement of circle averages after a relatively closed deletion
implies equality under either compact-containment alternative. -/
theorem IsLQGLimit.regularizedFamily_eq_of_relative_local_rank
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {U K : Set ℂ} {R t : ℝ} {z : ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : LocallyFiniteRankOn U K)
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
  regularizedFamily_eq_of_restrict_eq_of_relative_local_rank hμ hν hVμ hVν hU hUb hUR
    hD hK (hμlim.restrict_eq hνlim hD hloc) hqc hq ht hz hw hopenU hΛ hΛ' hcl

end HarmonicBalls
