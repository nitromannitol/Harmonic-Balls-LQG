import HarmonicBalls.Proofs.Sec5.LocallyFiniteRankInteriorAdmissibility

/-! # Admissibility for locally finite-rank deletions crossing the boundary -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- If the full-disc least supersolution vanishes at the interior removed points, it
is a competitor for the disc after a locally finite-rank deletion. -/
theorem leastSupersolution_mem_locallyFiniteRankOn_punctured_disc_of_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hzero : ∀ a ∈ K, a ∈ ball (0 : ℂ) R → leastSupersolution μ R z t a = 0) :
    leastSupersolution μ R z t ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hcl : closure (ball (0 : ℂ) R \ K) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨hw.1.mono hcl, hw.2.1.mono_set sdiff_subset, ?_⟩
  intro x hx hxz
  by_cases hxK : x ∈ K
  · have hxU : x ∉ ball (0 : ℂ) R \ K := fun h => h.2 hxK
    rw [greenFunction_of_notMem_right hxU, mul_zero]
    by_cases hxball : x ∈ ball (0 : ℂ) R
    · rw [hzero x hxK hxball]
    · have h1 := hw.2.2 x (hcl hx) hxz
      rw [greenFunction_of_notMem_right hxball, mul_zero] at h1
      exact h1
  · by_cases hxU : x ∈ ball (0 : ℂ) R \ K
    · rw [greenFunction_ball_sdiff_of_locallyFiniteRankOn hKclosed hK hz hxU hxz]
      exact hw.2.2 x (hcl hx) hxz
    · have hxb : x ∉ ball (0 : ℂ) R := fun hxb => hxU ⟨hxb, hxK⟩
      have h1 := hw.2.2 x (hcl hx) hxz
      rw [greenFunction_of_notMem_right hxb, mul_zero] at h1
      rw [greenFunction_of_notMem_right hxU, mul_zero]
      exact h1

/-- When the full-disc least supersolution vanishes on the interior deleted set, the
two least supersolutions agree throughout the closed disc, including the pole. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq_on_closedBall_of_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hzero : ∀ a ∈ K, a ∈ ball (0 : ℂ) R → leastSupersolution μ R z t a = 0) :
    EqOn (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (leastSupersolution μ R z t) (closedBall 0 R) := by
  obtain ⟨_, hvcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hvcomp := leastSupersolution_mem_locallyFiniteRankOn_punctured_disc_of_interior_zero hμ hR hV K hKclosed hK hz ht hzero
  intro x hx
  have hbound : ∀ w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t,
      leastSupersolution μ R z t x ≤ w x := by
    intro w hw
    have hw' : w ∈ supersolutions μ R z t := by
      have hw'' := locallyFiniteRankOn_punctured_supersolution_mem_domain hμ isOpen_ball
        isBounded_ball hK
        ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
        (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le hw
      simpa only [supersolutionsOn_ball μ hR.ne'] using hw'' 
    by_cases hxz : x = z
    · subst x
      exact leastSupersolution_le_at_pole_of_continuous hz.1 hvcont hw'
    · exact leastSupersolution_le hw' hx hxz
  have hbdd : BddBelow ((fun w : ℂ → ℝ => w x) ''
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) := by
    refine ⟨leastSupersolution μ R z t x, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw
  apply le_antisymm
  · exact csInf_le hbdd ⟨_, hvcomp, rfl⟩
  · apply le_csInf (show (((fun w : ℂ → ℝ => w x) ''
        supersolutionsOn μ (ball (0 : ℂ) R \ K) z t)).Nonempty from
          ⟨_, ⟨_, hvcomp, rfl⟩⟩)
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw

/-- The punctured-domain infimum is admissible exactly when the full-disc
least supersolution vanishes at each interior removed point. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_mem_iff_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
        supersolutionsOn μ (ball (0 : ℂ) R \ K) z t ↔
      ∀ a ∈ K, a ∈ ball (0 : ℂ) R → leastSupersolution μ R z t a = 0 := by
  constructor
  · intro hadm a ha haR
    by_contra hneq
    exact not_mem_supersolutionsOn_of_locallyFiniteRankOn_interior_puncture
      hμ hR hV K hKclosed hK haR ha hz ht hneq hadm
  · intro hzero
    have hw := leastSupersolution_mem_locallyFiniteRankOn_punctured_disc_of_interior_zero hμ hR hV K hKclosed hK hz ht hzero
    have heq := leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq_on_closedBall_of_interior_zero
      hμ hR hV K hKclosed hK hz ht hzero
    have hcl : closure (ball (0 : ℂ) R \ K) ⊆ closedBall (0 : ℂ) R :=
      closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
    have hU : IsOpen (ball (0 : ℂ) R \ K) :=
      isOpen_ball.sdiff hKclosed
    refine ⟨hw.1.congr (heq.mono hcl),
      hw.2.1.congr_eqOn hU.measurableSet (heq.symm.mono (sdiff_subset.trans ball_subset_closedBall)), ?_⟩
    intro x hx hxz
    rw [heq (hcl hx)]
    exact hw.2.2 x hx hxz


/-- Admissibility places all deleted interior points inside the full-disc cluster. -/
theorem inter_ball_subset_cluster_of_locallyFiniteRankOn_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) :
    K ∩ ball (0 : ℂ) R ⊆ cluster μ R z t := by
  have hzero := (leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_mem_iff_interior_zero
    hμ hR hV K hKclosed hK hz ht).mp hadm
  rintro a ⟨ha, haR⟩
  have hza : z ≠ a := fun h => hz.2 (h ▸ ha)
  refine ⟨haR, Or.inr ?_⟩
  rw [hzero a ha haR]
  have hg := greenFunction_ball_pos hz.1 haR hza
  nlinarith

/-- A deleted interior point and compact containment force the punctured
infimum to be inadmissible. -/
theorem not_mem_supersolutionsOn_locallyFiniteRankOn_punctured_of_interior_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hne : (K ∩ ball (0 : ℂ) R).Nonempty)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆
      ball (0 : ℂ) R \ K) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  intro hadm
  obtain ⟨a, ha, haR⟩ := hne
  have hac := inter_ball_subset_cluster_of_locallyFiniteRankOn_punctured_admissible
    hμ hR hV K hKclosed hK hz ht hadm ⟨ha, haR⟩
  have heq := closure_clusterOn_locallyFiniteRankOn_punctured_disc_eq hμ hR hV hKclosed hK hz ht
  have hboundary : a ∈ closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) :=
    heq.symm ▸ subset_closure hac
  exact (hcl hboundary).2 ha

#print axioms inter_ball_subset_cluster_of_locallyFiniteRankOn_punctured_admissible
#print axioms not_mem_supersolutionsOn_locallyFiniteRankOn_punctured_of_interior_compact_containment
#print axioms leastSupersolution_mem_locallyFiniteRankOn_punctured_disc_of_interior_zero
#print axioms leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_eq_on_closedBall_of_interior_zero
#print axioms leastSupersolutionOn_locallyFiniteRankOn_punctured_disc_mem_iff_interior_zero

end HarmonicBalls
