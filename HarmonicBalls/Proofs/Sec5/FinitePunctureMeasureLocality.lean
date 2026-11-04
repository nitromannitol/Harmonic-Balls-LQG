import HarmonicBalls.Proofs.Sec5.FinitePunctureStrongCompatibility
import HarmonicBalls.Proofs.Sec5.CountableDeletionLocality
import HarmonicBalls.Proofs.Sec5.FinitePunctureAdmissibility
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-! # Locality on finitely punctured discs

The cluster on a finitely punctured disc need not have an admissible least
supersolution. Its compact containment nevertheless suffices for locality of
regularized cluster families. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- Agreement of two measures on a finitely punctured disc determines their
regularized clusters if either the first regularized cluster or the first
punctured-domain cluster is compactly contained in that domain. -/
theorem regularizedFamily_eq_of_restrict_eq_finset_punctured_disc
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hμν : μ.restrict (ball (0 : ℂ) R \ (K : Set ℂ)) =
      ν.restrict (ball (0 : ℂ) R \ (K : Set ℂ)))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ (K : Set ℂ) ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) ⊆
        ball (0 : ℂ) R \ (K : Set ℂ)) :
    Λ t = Λ' t := by
  have hclosure : closure (Λ t) ⊆ ball (0 : ℂ) R := by
    rcases hcl with hcl | hcl
    · exact hcl.trans sdiff_subset
    · have heq := regularizedFamily_strongCompatibility_finset_punctured_disc
        hμ hVμ hR K hK hz ht hΛ (Or.inr hcl)
      rw [heq]
      exact hcl.trans sdiff_subset
  exact regularizedFamily_eq_of_restrict_sdiff_countable hμ hν hVμ hVν isOpen_ball
    K.countable_toSet hμν ht hΛ hΛ' hclosure

/-- The same locality conclusion follows from local agreement of the
approximating fields on the punctured disc. -/
theorem IsLQGLimit.regularizedFamily_eq_of_finset_punctured_disc
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ (K : Set ℂ) →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ (K : Set ℂ) ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) ⊆
        ball (0 : ℂ) R \ (K : Set ℂ)) :
    Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_finset_punctured_disc hμ hν hVμ hVν hR K hK hz ht
    (hμlim.restrict_eq hνlim (isOpen_ball.sdiff K.isClosed) hloc) hΛ hΛ' hcl

universe u

/-- With polynomially high probability, the unit disc punctured at `1/2`
has a compactly contained small-time cluster whose least supersolution is
not admissible. Thus the second locality alternative can hold without
admissibility. -/
theorem polyHighProb_punctured_cluster_compact_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T,
      closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t) ⊆
        ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)} ∧
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t}) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  apply (hsmall.inter_ae hV).mono
  intro T ω hω t ht
  let K : Finset ℂ := {(1 / 2 : ℂ)}
  have hK : (K : Set ℂ) ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have hx' : x = (1 / 2 : ℂ) := by simpa [K] using hx
    subst x
    norm_num [mem_ball_zero_iff]
  have hz : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ (K : Set ℂ) := by
    norm_num [K, mem_ball_zero_iff]
  have hbound := hω.1 t ht 0 (by norm_num : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2))
  have hdisc : closure (cluster (μ ω) 1 0 t) ⊆ ball (0 : ℂ) 1 \ (K : Set ℂ) := by
    intro x hx
    have hxsmall := hbound hx
    have hnorm : ‖x‖ < (1 / 4 : ℝ) := by
      norm_num [mem_ball_zero_iff] at hxsmall ⊢
      exact hxsmall
    refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
    intro hxa
    have hxa' : x = (1 / 2 : ℂ) := by simpa [K] using hxa
    subst x
    norm_num at hnorm
  have hpunc : closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ (K : Set ℂ)) 0 t) ⊆
      ball (0 : ℂ) 1 \ (K : Set ℂ) := by
    rw [closure_clusterOn_finset_punctured_disc_eq hω.2.1 zero_lt_one
      (hω.2.2 1 zero_lt_one) K hK hz ht.1]
    exact hdisc
  have hn := not_mem_supersolutionsOn_finset_punctured_of_compact_containment
    hω.2.1 zero_lt_one (hω.2.2 1 zero_lt_one) K (by simp [K]) hK hz ht.1 hpunc
  simpa [K] using And.intro hpunc hn

#print axioms polyHighProb_punctured_cluster_compact_not_admissible

#print axioms regularizedFamily_eq_of_restrict_eq_finset_punctured_disc
#print axioms IsLQGLimit.regularizedFamily_eq_of_finset_punctured_disc

end HarmonicBalls
