import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureAdmissibility
import HarmonicBalls.Proofs.Sec5.FinitePunctureMeasureLocality

/-! # Locality after locally finite point deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A set locally finite in a disc is countable within that disc. -/
theorem countable_inter_ball_of_locally_finite {R : ℝ} {K : Set ℂ}
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite) :
    (K ∩ ball (0 : ℂ) R).Countable := by
  let A : ℚ → Set ℂ := fun q => if (q : ℝ) < R then K ∩ closedBall 0 q else ∅
  have hA : ∀ q, (A q).Countable := by
    intro q
    dsimp [A]
    split_ifs with hq
    · exact (hK q hq).countable
    · exact Set.countable_empty
  apply (Set.countable_iUnion hA).mono
  intro x hx
  obtain ⟨q, hxq, hqR⟩ := exists_rat_btwn (mem_ball_zero_iff.mp hx.2)
  apply Set.mem_iUnion.mpr
  refine ⟨q, ?_⟩
  simp only [A, ite_eq_left hqR, mem_inter_iff]
  exact ⟨hx.1, mem_closedBall_zero_iff.mpr hxq.le⟩

/-- Agreement of measures on a locally finitely punctured disc determines
regularized clusters under either compact-containment alternative. -/
theorem regularizedFamily_eq_of_restrict_eq_locally_finite_punctured_disc
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {R t : ℝ} {z : ℂ} (hR : 0 < R) {K : Set ℂ}
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hμν : μ.restrict (ball (0 : ℂ) R \ K) = ν.restrict (ball (0 : ℂ) R \ K))
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball (0 : ℂ) R \ K) :
    Λ t = Λ' t := by
  have hclosure : closure (Λ t) ⊆ ball (0 : ℂ) R := by
    rcases hcl with hcl | hcl
    · exact hcl.trans sdiff_subset
    · have heq := regularizedFamily_strongCompatibility_locally_finite_punctured_disc
        hμ hVμ hR hK hz ht hΛ (Or.inr hcl)
      rw [heq]
      exact hcl.trans sdiff_subset
  have hμν' : μ.restrict (ball (0 : ℂ) R \ (K ∩ ball (0 : ℂ) R)) =
      ν.restrict (ball (0 : ℂ) R \ (K ∩ ball (0 : ℂ) R)) := by
    have hset : ball (0 : ℂ) R \ (K ∩ ball (0 : ℂ) R) = ball (0 : ℂ) R \ K := by
      ext x
      simp
    rw [hset]
    exact hμν
  exact regularizedFamily_eq_of_restrict_sdiff_countable hμ hν hVμ hVν isOpen_ball
    (countable_inter_ball_of_locally_finite hK) hμν' ht hΛ hΛ' hclosure

/-- The same conclusion holds when approximating fields agree locally on the
locally finitely punctured disc. -/
theorem IsLQGLimit.regularizedFamily_eq_of_locally_finite_punctured_disc
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {βm βp βm' βp' : ℝ}
    (hVμ : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    (hVν : ∀ r : ℝ, 0 < r → VolumeGrowth ν r βm' βp')
    {R t : ℝ} {z : ℂ} (hR : 0 < R) {K : Set ℂ}
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x)
    {Λ Λ' : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hΛ' : IsRegularizedClusterFamily ν Λ' z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball (0 : ℂ) R \ K) :
    Λ t = Λ' t :=
  regularizedFamily_eq_of_restrict_eq_locally_finite_punctured_disc hμ hν hVμ hVν hR hK hz ht
    (hμlim.restrict_eq hνlim (isOpen_locally_finite_punctured_ball hK) hloc) hΛ hΛ' hcl

/-- Agreement off a locally finite set determines all clusters in the disc. -/
theorem cluster_eq_of_restrict_locally_finite_punctured_disc
    {μ ν : Measure ℂ} {R βm βp βm' βp' : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R βm' βp')
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hμν : μ.restrict (ball (0 : ℂ) R \ K) = ν.restrict (ball (0 : ℂ) R \ K))
    (z : ℂ) (t : ℝ) : cluster μ R z t = cluster ν R z t := by
  have hset : ball (0 : ℂ) R \ (K ∩ ball (0 : ℂ) R) = ball (0 : ℂ) R \ K := by
    ext x
    simp
  apply cluster_eq_of_restrict_sdiff_countable hR hVμ hVν
    (countable_inter_ball_of_locally_finite hK) inter_subset_right
  simpa only [hset] using hμν

/-- Agreement on a locally finitely punctured disc determines its cluster at
all positive times, without a compact-containment assumption. -/
theorem clusterOn_eq_of_restrict_locally_finite_punctured_disc
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp βm' βp' t : ℝ} {z : ℂ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R βm' βp')
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hμν : μ.restrict (ball (0 : ℂ) R \ K) = ν.restrict (ball (0 : ℂ) R \ K)) :
    clusterOn μ (ball (0 : ℂ) R \ K) z t = clusterOn ν (ball (0 : ℂ) R \ K) z t := by
  rw [clusterOn_locally_finite_punctured_disc_eq_sdiff hμ hR hVμ hK hz ht,
    clusterOn_locally_finite_punctured_disc_eq_sdiff hν hR hVν hK hz ht,
    cluster_eq_of_restrict_locally_finite_punctured_disc hR hVμ hVν hK hμν z t]

/-- Local agreement of approximating fields determines the cluster of the
locally finitely punctured disc at all positive times. -/
theorem IsLQGLimit.clusterOn_eq_of_locally_finite_punctured_disc
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμlim : IsLQGLimit γ hε μ) (hνlim : IsLQGLimit γ hε' ν)
    (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp βm' βp' t : ℝ} {z : ℂ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R βm' βp')
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hloc : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ K →
      ∀ᶠ k : ℕ in atTop, ∀ x ∈ C, hε (dyadicScale k) x = hε' (dyadicScale k) x) :
    clusterOn μ (ball (0 : ℂ) R \ K) z t = clusterOn ν (ball (0 : ℂ) R \ K) z t :=
  clusterOn_eq_of_restrict_locally_finite_punctured_disc hμ hν hR hVμ hVν hK hz ht
    (hμlim.restrict_eq hνlim (isOpen_locally_finite_punctured_ball hK) hloc)

end HarmonicBalls
