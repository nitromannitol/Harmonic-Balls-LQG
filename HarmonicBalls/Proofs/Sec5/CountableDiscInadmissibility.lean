import HarmonicBalls.Proofs.Sec5.RelativeCountableAdmissibility
import HarmonicBalls.Proofs.Sec5.AllCentrePunctureInadmissibility

/-! # Inadmissibility after countable deletions from a disc

The exceptional set may accumulate throughout the disc, provided it is
relatively closed and countable. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- On a disc, the infimum after a relatively closed countable deletion is
admissible exactly when the disc least supersolution vanishes at every
deleted interior point. -/
theorem leastSupersolutionOn_relative_countable_disc_mem_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t ↔
      ∀ a ∈ K, a ∈ ball (0 : ℂ) R → leastSupersolution μ R z t a = 0 := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hleq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hw' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [hleq, supersolutionsOn_ball μ hR.ne']
    exact hw
  have hcontain : closure (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) (R + 1) :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  have h := leastSupersolutionOn_mem_sdiff_iff_relative_countable_interior_zero
    hμ isOpen_ball isBounded_ball hcontain hD hK hz
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le hw'
  simpa only [hleq] using h

/-- At each deleted interior point, the punctured infimum tends along the
punctured domain to the full-disc least supersolution. -/
theorem tendsto_leastSupersolutionOn_relative_countable_disc_at_deleted
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (haK : a ∈ K) (ha : a ∈ ball (0 : ℂ) R) :
    Tendsto (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) := by
  obtain ⟨_, hc, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hleq : leastSupersolutionOn μ (ball (0 : ℂ) R) z t = leastSupersolution μ R z t := by
    funext x
    simp only [leastSupersolutionOn, leastSupersolution, supersolutionsOn_ball μ hR.ne']
  have hw' : leastSupersolutionOn μ (ball (0 : ℂ) R) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R) z t := by
    rw [hleq, supersolutionsOn_ball μ hR.ne']
    exact hw
  have hcontain : closure (ball (0 : ℂ) R) ⊆ ball (0 : ℂ) (R + 1) :=
    (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
      (closedBall_subset_ball (by linarith))
  let L := closure (ball (0 : ℂ) R ∩ K)
  have hDL : ball (0 : ℂ) R \ L = ball (0 : ℂ) R \ K :=
    sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hL : (L ∩ ball (0 : ℂ) R).Countable := by
    dsimp [L]
    simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK
  have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
  have hfull : Tendsto (leastSupersolution μ R z t)
      (𝓝[ball (0 : ℂ) R \ K] a) (𝓝 (leastSupersolution μ R z t a)) :=
    (hc a (ball_subset_closedBall ha)).mono (sdiff_subset.trans ball_subset_closedBall)
  apply hfull.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ K] a ≤ 𝓝 a)] with x hx hxz
  have hxL : x ∈ ball (0 : ℂ) R \ L := by rwa [hDL]
  have heq := leastSupersolutionOn_sdiff_eq_of_local_countable hμ isOpen_ball isBounded_ball
    hcontain isClosed_closure hL
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) ht.le
    (show z ∈ ball (0 : ℂ) R \ L from by rwa [hDL]) hw' hxL hxz
  change leastSupersolutionOn μ (ball (0 : ℂ) R \ L) z t x =
    leastSupersolutionOn μ (ball (0 : ℂ) R) z t x at heq
  rw [hDL, hleq] at heq
  exact heq.symm

/-- Continuity at a deleted point is equivalent to vanishing of the
full-disc least supersolution there. -/
theorem continuousWithinAt_relative_countable_disc_infimum_iff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (haK : a ∈ K) (ha : a ∈ ball (0 : ℂ) R) :
    ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t)
      (ball (0 : ℂ) R \ K) a ↔ leastSupersolution μ R z t a = 0 := by
  let L := closure (ball (0 : ℂ) R ∩ K)
  have hDL : ball (0 : ℂ) R \ L = ball (0 : ℂ) R \ K :=
    sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hL : (L ∩ ball (0 : ℂ) R).Countable := by
    dsimp [L]
    simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK
  have hcl : closure (ball (0 : ℂ) R \ K) = closure (ball (0 : ℂ) R) := by
    rw [← hDL]
    exact closure_sdiff_countable_inter isOpen_ball hL
  have hac : a ∈ closure (ball (0 : ℂ) R \ K) := by rw [hcl]; exact subset_closure ha
  have : (𝓝[ball (0 : ℂ) R \ K] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
  have hzero := leastSupersolutionOn_eq_zero_of_boundary (μ := μ)
    (isBounded_ball.subset sdiff_subset) ht.le hac (by exact fun h => h.2 haK) haz
  have hlim := tendsto_leastSupersolutionOn_relative_countable_disc_at_deleted
    hμ hR hV K hD hK hz ht haK ha
  constructor
  · intro hc
    exact (tendsto_nhds_unique hlim hc).trans hzero
  · intro h
    change Tendsto _ _ (𝓝 (leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t a))
    simpa [h, hzero] using hlim

universe u

/-- Almost surely, at every deleted interior point the punctured infimum
is discontinuous relative to the punctured disc, simultaneously for all
centres, positive times and relatively closed countable deletions. -/
theorem ae_relative_countable_disc_infimum_discontinuous_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      IsOpen (ball (0 : ℂ) 1 \ K) → (K ∩ ball (0 : ℂ) 1).Countable →
      z ∉ K → ∀ a ∈ K, a ∈ ball (0 : ℂ) 1 → ∀ t : ℝ, 0 < t →
      ¬ ContinuousWithinAt (leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t)
        (ball (0 : ℂ) 1 \ K) a := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hD hK hzK a haK ha t ht hc
  have haz : a ≠ z := fun h => hzK (h ▸ haK)
  have heq := (continuousWithinAt_relative_countable_disc_infimum_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hD hK ⟨hz, hzK⟩ ht haK ha).mp hc
  exact (ne_of_lt (hneg z hz a ha haz t ht)) heq

/-- Almost surely, simultaneously for all centres and positive times, a
nonempty relatively closed countable deletion from the unit disc makes the
punctured least supersolution inadmissible. The field invariance and coordinate
change inputs are staged. -/
theorem ae_relative_countable_disc_infimum_inadmissible_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      IsOpen (ball (0 : ℂ) 1 \ K) → (K ∩ ball (0 : ℂ) 1).Countable →
      (K ∩ ball (0 : ℂ) 1).Nonempty → z ∉ K → ∀ t : ℝ, 0 < t →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hD hK hne hzK t ht hadm
  obtain ⟨a, haK, haU⟩ := hne
  have haz : a ≠ z := fun h => hzK (h ▸ haK)
  have heq := (leastSupersolutionOn_relative_countable_disc_mem_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hD hK ⟨hz, hzK⟩ ht).mp hadm a haK haU
  exact (ne_of_lt (hneg z hz a haU haz t ht)) heq


end HarmonicBalls
