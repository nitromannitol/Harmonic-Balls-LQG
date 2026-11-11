import HarmonicBalls.Proofs.Sec5.FinitePunctureStrongCompatibility

/-! # Admissibility after removing finitely many points -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- Continuity extends the least-supersolution comparison to the pole. -/
theorem leastSupersolution_le_at_pole_of_continuous
    {μ : Measure ℂ} {R t : ℝ} {z : ℂ} {w : ℂ → ℝ}
    (hz : z ∈ ball (0 : ℂ) R)
    (hv : ContinuousOn (leastSupersolution μ R z t) (closedBall 0 R))
    (hw : w ∈ supersolutions μ R z t) :
    leastSupersolution μ R z t z ≤ w z := by
  have hn : closedBall (0 : ℂ) R ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hvc := (hv z (ball_subset_closedBall hz)).continuousAt hn
  have hwc := (hw.1 z (ball_subset_closedBall hz)).continuousAt hn
  have : (𝓝[{z}ᶜ] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp ((dense_compl_singleton z) z)
  apply le_of_tendsto_of_tendsto (b := 𝓝[{z}ᶜ] z)
    (hvc.tendsto.mono_left nhdsWithin_le_nhds)
    (hwc.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds : 𝓝[{z}ᶜ] z ≤ 𝓝 z) (isOpen_ball.mem_nhds hz)] with x hx hxball
  exact leastSupersolution_le hw (ball_subset_closedBall hxball) (by simpa using hx)

/-- If the full-disc least supersolution vanishes at the removed points, it
is a competitor for the finitely punctured disc. -/
theorem leastSupersolution_mem_finset_punctured_disc_of_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hzero : ∀ a ∈ K, leastSupersolution μ R z t a = 0) :
    leastSupersolution μ R z t ∈ supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hcl : closure (ball (0 : ℂ) R \ (K : Set ℂ)) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨hw.1.mono hcl, hw.2.1.mono_set sdiff_subset, ?_⟩
  intro x hx hxz
  by_cases hxK : x ∈ K
  · have hxU : x ∉ ball (0 : ℂ) R \ (K : Set ℂ) := fun h => h.2 hxK
    rw [greenFunction_of_notMem_right hxU, mul_zero, hzero x hxK]
  · by_cases hxU : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)
    · rw [greenFunction_finset_punctured_ball K hK hz hxU hxz]
      exact hw.2.2 x (hcl hx) hxz
    · have hxb : x ∉ ball (0 : ℂ) R := fun hxb => hxU ⟨hxb, hxK⟩
      have h1 := hw.2.2 x (hcl hx) hxz
      rw [greenFunction_of_notMem_right hxb, mul_zero] at h1
      rw [greenFunction_of_notMem_right hxU, mul_zero]
      exact h1

/-- When the full-disc least supersolution vanishes on the deleted set, the
two least supersolutions agree throughout the closed disc, including the pole. -/
theorem leastSupersolutionOn_finset_punctured_disc_eq_on_closedBall_of_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hzero : ∀ a ∈ K, leastSupersolution μ R z t a = 0) :
    EqOn (leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t)
      (leastSupersolution μ R z t) (closedBall 0 R) := by
  obtain ⟨_, hvcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hvcomp := leastSupersolution_mem_finset_punctured_disc_of_zero hμ hR hV K hK hz ht hzero
  intro x hx
  have hbound : ∀ w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t,
      leastSupersolution μ R z t x ≤ w x := by
    intro w hw
    have hw' := finite_punctured_disc_supersolution_mem_disc hμ hR hV ht.le K hw
    by_cases hxz : x = z
    · subst x
      exact leastSupersolution_le_at_pole_of_continuous hz.1 hvcont hw'
    · exact leastSupersolution_le hw' hx hxz
  have hbdd : BddBelow ((fun w : ℂ → ℝ => w x) ''
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) := by
    refine ⟨leastSupersolution μ R z t x, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw
  apply le_antisymm
  · exact csInf_le hbdd ⟨_, hvcomp, rfl⟩
  · apply le_csInf (show (((fun w : ℂ → ℝ => w x) ''
        supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t)).Nonempty from
          ⟨_, ⟨_, hvcomp, rfl⟩⟩)
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw

/-- The punctured-domain infimum is admissible exactly when the full-disc
least supersolution vanishes at each removed point. -/
theorem leastSupersolutionOn_finset_punctured_disc_mem_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∈
        supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ↔
      ∀ a ∈ K, leastSupersolution μ R z t a = 0 := by
  constructor
  · exact leastSupersolution_eq_zero_of_finset_punctured_admissible hμ hR hV K hK hz ht
  · intro hzero
    have hw := leastSupersolution_mem_finset_punctured_disc_of_zero hμ hR hV K hK hz ht hzero
    have heq := leastSupersolutionOn_finset_punctured_disc_eq_on_closedBall_of_zero
      hμ hR hV K hK hz ht hzero
    have hcl : closure (ball (0 : ℂ) R \ (K : Set ℂ)) ⊆ closedBall (0 : ℂ) R :=
      closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
    have hU : IsOpen (ball (0 : ℂ) R \ (K : Set ℂ)) :=
      isOpen_ball.sdiff K.finite_toSet.isClosed
    refine ⟨hw.1.congr (heq.mono hcl),
      hw.2.1.congr_eqOn hU.measurableSet (heq.symm.mono (sdiff_subset.trans ball_subset_closedBall)), ?_⟩
    intro x hx hxz
    rw [heq (hcl hx)]
    exact hw.2.2 x hx hxz

/-- Admissibility places every removed point inside the full-disc cluster. -/
theorem finset_subset_cluster_of_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) :
    (K : Set ℂ) ⊆ cluster μ R z t := by
  have hzero := (leastSupersolutionOn_finset_punctured_disc_mem_iff
    hμ hR hV K hK hz ht).mp hadm
  intro a ha
  have hza : z ≠ a := fun h => hz.2 (h ▸ ha)
  refine ⟨hK ha, Or.inr ?_⟩
  rw [hzero a ha]
  have hg := greenFunction_ball_pos hz.1 (hK ha) hza
  nlinarith

/-- A nonempty puncture set and compact containment force the punctured
infimum to be inadmissible. -/
theorem not_mem_supersolutionsOn_finset_punctured_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ) (hne : K.Nonempty)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) ⊆
      ball (0 : ℂ) R \ (K : Set ℂ)) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  intro hadm
  obtain ⟨a, ha⟩ := hne
  have hac := finset_subset_cluster_of_punctured_admissible hμ hR hV K hK hz ht hadm ha
  have heq := closure_clusterOn_finset_punctured_disc_eq hμ hR hV K hK hz ht
  have hboundary : a ∈ closure (clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t) :=
    heq.symm ▸ subset_closure hac
  exact (hcl hboundary).2 ha



end HarmonicBalls
