import HarmonicBalls.Proofs.Sec5.AccumulationDiscCompatibility
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureAdmissibility

/-! # Admissibility for deletions with locally finite accumulation -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- At a deleted point, the punctured infimum tends to the full-disc least
supersolution along the punctured disc. -/
theorem tendsto_leastSupersolutionOn_accumulating_punctured_disc_at_puncture
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) := by
  obtain ⟨_, hcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hfull : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) :=
    (hcont a (ball_subset_closedBall (hKR ha))).mono (sdiff_subset.trans ball_subset_closedBall)
  apply hfull.congr'
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ K] a ≤ 𝓝 a)] with x hx hxz
  exact (leastSupersolutionOn_accumulating_punctured_disc_eq hμ hR hV hKclosed hLclosed hL hK hz ht hx hxz).symm

/-- The punctured infimum is continuous at a deleted point exactly when the
full-disc least supersolution vanishes there. -/
theorem continuousWithinAt_accumulating_punctured_infimum_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
        (ball (0 : ℂ) R \ K) a ↔ leastSupersolution μ R z t a = 0 := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ K) := by
    rw [closure_sdiff_countable_inter isOpen_ball
      (countable_inter_open_of_locally_finite_accumulation isOpen_ball hLclosed hL hK),
      closure_ball (0 : ℂ) hR.ne']
    exact ball_subset_closedBall (hKR ha)
  have : (𝓝[ball (0 : ℂ) R \ K] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  have hzero := leastSupersolutionOn_eq_zero_of_boundary
    (μ := μ) (isBounded_ball.subset sdiff_subset) ht.le hac (by simp [ha]) haz
  have hlim := tendsto_leastSupersolutionOn_accumulating_punctured_disc_at_puncture hμ hR hV K hKclosed hLclosed hL hK hKR ha hz ht
  constructor
  · intro hc
    exact (tendsto_nhds_unique hlim hc).trans hzero
  · intro h
    change Tendsto _ _ (𝓝 (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t a))
    simpa [h, hzero] using hlim

/-- Admissibility forces the full-disc least supersolution to vanish at every
removed point. -/
theorem leastSupersolution_eq_zero_of_accumulating_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) :
    ∀ a ∈ K, leastSupersolution μ R z t a = 0 := by
  intro a ha
  have hac : a ∈ closure (ball (0 : ℂ) R \ K) := by
    rw [closure_sdiff_countable_inter isOpen_ball
      (countable_inter_open_of_locally_finite_accumulation isOpen_ball hLclosed hL hK),
      closure_ball (0 : ℂ) hR.ne']
    exact ball_subset_closedBall (hKR ha)
  exact (continuousWithinAt_accumulating_punctured_infimum_iff hμ hR hV K hKclosed hLclosed hL hK hKR ha hz ht).mp
    ((hadm.1 a hac).mono subset_closure)

/-- If the full-disc least supersolution vanishes at the removed points, it
is a competitor for the disc with an accumulating deletion. -/
theorem leastSupersolution_mem_accumulating_punctured_disc_of_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (_hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (_hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hzero : ∀ a ∈ K, leastSupersolution μ R z t a = 0) :
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
    rw [greenFunction_of_notMem_right hxU, mul_zero, hzero x hxK]
  · by_cases hxU : x ∈ ball (0 : ℂ) R \ K
    · rw [greenFunction_ball_sdiff_of_locally_finite_accumulation hKclosed hL hK hz hxU hxz]
      exact hw.2.2 x (hcl hx) hxz
    · have hxb : x ∉ ball (0 : ℂ) R := fun hxb => hxU ⟨hxb, hxK⟩
      have h1 := hw.2.2 x (hcl hx) hxz
      rw [greenFunction_of_notMem_right hxb, mul_zero] at h1
      rw [greenFunction_of_notMem_right hxU, mul_zero]
      exact h1

/-- When the full-disc least supersolution vanishes on the deleted set, the
two least supersolutions agree throughout the closed disc, including the pole. -/
theorem leastSupersolutionOn_accumulating_punctured_disc_eq_on_closedBall_of_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hzero : ∀ a ∈ K, leastSupersolution μ R z t a = 0) :
    EqOn (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (leastSupersolution μ R z t) (closedBall 0 R) := by
  obtain ⟨_, hvcont, _⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hvcomp := leastSupersolution_mem_accumulating_punctured_disc_of_zero hμ hR hV K hKclosed hLclosed hL hK hKR hz ht hzero
  intro x hx
  have hbound : ∀ w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t,
      leastSupersolution μ R z t x ≤ w x := by
    intro w hw
    have hw' := accumulating_punctured_disc_supersolution_mem_disc hμ hR hV ht.le hLclosed hL hK hw
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
least supersolution vanishes at each removed point. -/
theorem leastSupersolutionOn_accumulating_punctured_disc_mem_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
        supersolutionsOn μ (ball (0 : ℂ) R \ K) z t ↔
      ∀ a ∈ K, leastSupersolution μ R z t a = 0 := by
  constructor
  · exact leastSupersolution_eq_zero_of_accumulating_punctured_admissible hμ hR hV K hKclosed hLclosed hL hK hKR hz ht
  · intro hzero
    have hw := leastSupersolution_mem_accumulating_punctured_disc_of_zero hμ hR hV K hKclosed hLclosed hL hK hKR hz ht hzero
    have heq := leastSupersolutionOn_accumulating_punctured_disc_eq_on_closedBall_of_zero
      hμ hR hV K hKclosed hLclosed hL hK hKR hz ht hzero
    have hcl : closure (ball (0 : ℂ) R \ K) ⊆ closedBall (0 : ℂ) R :=
      closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
    have hU : IsOpen (ball (0 : ℂ) R \ K) :=
      isOpen_ball.sdiff hKclosed
    refine ⟨hw.1.congr (heq.mono hcl),
      hw.2.1.congr_eqOn hU.measurableSet (heq.symm.mono (sdiff_subset.trans ball_subset_closedBall)), ?_⟩
    intro x hx hxz
    rw [heq (hcl hx)]
    exact hw.2.2 x hx hxz

/-- Admissibility places every removed point inside the full-disc cluster. -/
theorem accumulating_subset_cluster_of_punctured_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) :
    K ⊆ cluster μ R z t := by
  have hzero := (leastSupersolutionOn_accumulating_punctured_disc_mem_iff
    hμ hR hV K hKclosed hLclosed hL hK hKR hz ht).mp hadm
  intro a ha
  have hza : z ≠ a := fun h => hz.2 (h ▸ ha)
  refine ⟨hKR ha, Or.inr ?_⟩
  rw [hzero a ha]
  have hg := greenFunction_ball_pos hz.1 (hKR ha) hza
  nlinarith

/-- A nonempty puncture set and compact containment force the punctured
infimum to be inadmissible. -/
theorem not_mem_supersolutionsOn_accumulating_punctured_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ) (hne : K.Nonempty)
    {L : Set ℂ} (hKclosed : IsClosed K) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆
      ball (0 : ℂ) R \ K) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  intro hadm
  obtain ⟨a, ha⟩ := hne
  have hac := accumulating_subset_cluster_of_punctured_admissible hμ hR hV K hKclosed hLclosed hL hK hKR hz ht hadm ha
  have heq := closure_clusterOn_accumulating_punctured_disc_eq hμ hR hV hKclosed hLclosed hL hK hz ht
  have hboundary : a ∈ closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) :=
    heq.symm ▸ subset_closure hac
  exact (hcl hboundary).2 ha



end HarmonicBalls
