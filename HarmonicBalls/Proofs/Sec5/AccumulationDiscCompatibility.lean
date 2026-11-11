import HarmonicBalls.Proofs.Sec5.AccumulationSubharmonicMaximum
import HarmonicBalls.Proofs.Sec5.AccumulationCompetitors

/-! # Disc clusters after deleting accumulating point sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- For a closed deletion, possible accumulation points outside the deletion
can be discarded from the accumulation set. -/
theorem locally_finite_off_inter_closed_deletion
    {U K L : Set ℂ} (hKclosed : IsClosed K)
    (hK : ∀ D : Set ℂ, IsCompact D → D ⊆ U \ L → (K ∩ D).Finite) :
    ∀ D : Set ℂ, IsCompact D → D ⊆ U \ (L ∩ K) → (K ∩ D).Finite := by
  intro D hD hDU
  have hcompact : IsCompact (D ∩ K) := hD.inter_right hKclosed
  have hsub : D ∩ K ⊆ U \ L := by
    intro y hy
    refine ⟨(hDU hy.1).1, ?_⟩
    intro hyL
    exact (hDU hy.1).2 ⟨hyL, hy.2⟩
  exact (hK (D ∩ K) hcompact hsub).subset (fun y hy => ⟨hy.1, hy.2, hy.1⟩)

/-- For a closed deletion with locally finite accumulation the punctured and
full-disc least supersolutions agree away from the deletion and pole. -/
theorem leastSupersolutionOn_accumulating_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K L : Set ℂ}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x = leastSupersolution μ R z t x := by
  have hL' : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → ((L ∩ K) ∩ C).Finite := by
    intro C hC hCU
    exact (hL C hC hCU).subset (fun _ hy => ⟨hy.1.1, hy.2⟩)
  have hK' := locally_finite_off_inter_closed_deletion hKclosed hK
  have hxL' : x ∉ L ∩ K := fun hy => hx.2 hy.2
  apply leastSupersolutionOn_accumulating_punctured_disc_eq_of_green_eq hμ hR hV
    (hLclosed.inter hKclosed) hL' hK' hz ht hx hxL' hxz
  intro y hy hyz
  exact greenFunction_ball_sdiff_of_locally_finite_accumulation hKclosed hL hK hz hy hyz

/-- Deleting the point set removes exactly those points from the disc cluster. -/
theorem clusterOn_accumulating_punctured_disc_eq_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K L : Set ℂ}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    clusterOn μ (ball (0 : ℂ) R \ K) z t = cluster μ R z t \ K := by
  ext x
  constructor
  · rintro ⟨hx, hxz | hxpos⟩
    · exact ⟨⟨hx.1, Or.inl hxz⟩, hx.2⟩
    · refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_ball_sdiff_of_locally_finite_accumulation hKclosed hL hK hz hx hxz,
          leastSupersolutionOn_accumulating_punctured_disc_eq hμ hR hV hKclosed hLclosed
            hL hK hz ht hx hxz] at hxpos
        exact hxpos
  · rintro ⟨⟨hx, hxz | hxpos⟩, hxK⟩
    · exact ⟨⟨hx, hxK⟩, Or.inl hxz⟩
    · refine ⟨⟨hx, hxK⟩, ?_⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_ball_sdiff_of_locally_finite_accumulation hKclosed hL hK hz ⟨hx, hxK⟩ hxz,
          leastSupersolutionOn_accumulating_punctured_disc_eq hμ hR hV hKclosed hLclosed
            hL hK hz ht ⟨hx, hxK⟩ hxz]
        exact hxpos

/-- The punctured and full-disc cluster closures coincide. -/
theorem closure_clusterOn_accumulating_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K L : Set ℂ}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_accumulating_punctured_disc_eq_sdiff hμ hR hV hKclosed hLclosed hL hK hz ht]
  apply closure_sdiff_countable_inter
  · rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht
  · exact (countable_inter_open_of_locally_finite_accumulation isOpen_ball hLclosed hL hK).mono
      (show K ∩ cluster μ R z t ⊆ K ∩ ball (0 : ℂ) R from
        fun _ hx => ⟨hx.1, cluster_subset_ball hx.2⟩)

/-- Strong compatibility holds under either compact-containment alternative. -/
theorem regularizedFamily_strongCompatibility_accumulating_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) {K L : Set ℂ}
    (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) := by
  have hc := closure_clusterOn_accumulating_punctured_disc_eq hμ hR (hV R hR)
    hKclosed hLclosed hL hK hz ht
  have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
    intro r hr hzr
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hV r hr) z hzr t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr (hV r hr) hzr ht
  rcases hcl with hΛcl | hcl
  · have hΛR := hΛcl.trans sdiff_subset
    have heq := hΛ.2.2 t ht R hR hΛR R le_rfl
    rw [heq, closure_regularizedCluster_eq_of_isOpen (hopen R hR hz.1), hc]
  · have hdisc : closure (cluster μ R z t) ⊆ ball (0 : ℂ) R := by
      rw [← hc]
      exact hcl.trans sdiff_subset
    have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR (hV R hR) hz.1 ht).2.2
    rw [hc]
    exact regularizedFamily_closure_eq_discCluster_of_compact_containment
      hR hz.1 ht hΛ hopen hv hdisc


end HarmonicBalls
