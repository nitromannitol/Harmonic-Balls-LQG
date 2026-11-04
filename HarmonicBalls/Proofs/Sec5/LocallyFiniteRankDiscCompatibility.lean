import HarmonicBalls.Proofs.Sec5.LocallyFiniteRankGreen
import HarmonicBalls.Proofs.Sec5.FiniteRankDiscCompatibility

/-! # Disc clusters after locally finite-rank point deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Locally finite-rank capped barriers give the reverse comparison away from the
deleted set and the pole. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_le_supersolution
    {μ : Measure ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ} {K : Set ℂ}
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K)
    (hxz : x ≠ z) (hw : w ∈ supersolutions μ R z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x ≤ w x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨ρ, hρ, htail⟩ := supersolution_lower_bound_near_sphere hz.1 hw hδ
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hw.1
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  obtain ⟨b, hbc, hbΔ, hbn, hsmall, hcover⟩ :=
    exists_capped_barrier_of_locallyFiniteRankOn hKc hK
      (C := closedBall (0 : ℂ) ρ) (isCompact_closedBall _ _) (closedBall_subset_ball hρ)
      hx.2 hM hδ
  have hcl : closure (ball (0 : ℂ) R \ K) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  let v : ℂ → ℝ := fun y => w y + δ + b y
  have hv : v ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
    refine ⟨((hw.1.add continuousOn_const).add hbc).mono hcl, ?_, ?_⟩
    · have hc := hasLaplacian_zero_of_harmonicOnNhd (U := ball (0 : ℂ) R) isOpen_ball
        (harmonicOnNhd_const (1 : ℝ))
      have hwδ : LaplacianLE (fun y => w y + δ) μ (ball (0 : ℂ) R) := by
        simpa only [mul_one] using hw.2.1.add_const_mul_of_hasLaplacian_zero hc δ
      exact (hwδ.add_of_nonpos hbΔ).mono_set sdiff_subset
    · intro y hy hyz
      have hycl := hcl hy
      by_cases hyK : y ∈ K
      · have hynot : y ∉ ball (0 : ℂ) R \ K := fun h => h.2 hyK
        rw [greenFunction_of_notMem_right hynot, mul_zero]
        by_cases hyρ : y ∈ closedBall (0 : ℂ) ρ
        · have hcov := hcover y ⟨hyK, hyρ⟩
          have hbound : ‖w y‖ ≤ M := (hB y hycl).trans (le_max_left B 0)
          have habs : -‖w y‖ ≤ w y := by simpa only [Real.norm_eq_abs] using neg_abs_le (w y)
          dsimp [v]
          linarith
        · have hyρ' : ρ < ‖y‖ := by
            rw [mem_closedBall_zero_iff] at hyρ
            exact lt_of_not_ge hyρ
          dsimp [v]
          linarith [htail y hycl hyρ', hbn y]
      · by_cases hyball : y ∈ ball (0 : ℂ) R
        · rw [greenFunction_ball_sdiff_of_locallyFiniteRankOn hKc hK hz ⟨hyball, hyK⟩ hyz]
          dsimp [v]
          linarith [hw.2.2 y hycl hyz, hbn y]
        · have hynot : y ∉ ball (0 : ℂ) R \ K := fun h => hyball h.1
          have hwbound := hw.2.2 y hycl hyz
          rw [greenFunction_of_notMem_right hyball, mul_zero] at hwbound
          rw [greenFunction_of_notMem_right hynot, mul_zero]
          dsimp [v]
          linarith [hbn y]
  have hle := leastSupersolutionOn_le_of_mem hv (subset_closure hx) hxz
  dsimp [v, δ] at hle hsmall ⊢
  linarith

/-- The punctured and full-disc least supersolutions agree away from the
deletion and the pole. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x = leastSupersolution μ R z t x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  apply le_antisymm (leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_le_supersolution
    hKc hK hz hx hxz hw)
  have hle := leastSupersolutionOn_le_locallyFiniteRankOn_punctured hμ isOpen_ball isBounded_ball hK
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le (subset_closure hx.1) hxz
  simpa only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne'] using hle

/-- Deleting the point set removes exactly those points from the disc cluster. -/
theorem clusterOn_locallyFiniteRankOn_punctured_disc_eq_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
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
        rw [greenFunction_ball_sdiff_of_locallyFiniteRankOn hKclosed hK hz hx hxz,
          leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq hμ hR hV hKclosed hK hz ht hx hxz] at hxpos
        exact hxpos
  · rintro ⟨⟨hx, hxz | hxpos⟩, hxK⟩
    · exact ⟨⟨hx, hxK⟩, Or.inl hxz⟩
    · refine ⟨⟨hx, hxK⟩, ?_⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_ball_sdiff_of_locallyFiniteRankOn hKclosed hK hz ⟨hx, hxK⟩ hxz,
          leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq hμ hR hV hKclosed hK hz ht ⟨hx, hxK⟩ hxz]
        exact hxpos

/-- The punctured and full-disc cluster closures coincide. -/
theorem closure_clusterOn_locallyFiniteRankOn_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_locallyFiniteRankOn_punctured_disc_eq_sdiff hμ hR hV hKclosed hK hz ht]
  apply closure_sdiff_countable_inter
  · rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht
  · exact (countable_inter_open_of_locallyFiniteRankOn isOpen_ball hK).mono
      (show K ∩ cluster μ R z t ⊆ K ∩ ball (0 : ℂ) R from
        fun _ hx => ⟨hx.1, cluster_subset_ball hx.2⟩)

/-- Strong compatibility holds under either compact-containment alternative. -/
theorem regularizedFamily_strongCompatibility_locallyFiniteRankOn_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) {K : Set ℂ}
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) := by
  have hc := closure_clusterOn_locallyFiniteRankOn_punctured_disc_eq hμ hR (hV R hR)
    hKclosed hK hz ht
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

#print axioms leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_le_supersolution
#print axioms leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq
#print axioms clusterOn_locallyFiniteRankOn_punctured_disc_eq_sdiff
#print axioms closure_clusterOn_locallyFiniteRankOn_punctured_disc_eq
#print axioms regularizedFamily_strongCompatibility_locallyFiniteRankOn_punctured_disc

end HarmonicBalls
