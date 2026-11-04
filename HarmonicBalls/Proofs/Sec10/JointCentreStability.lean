import HarmonicBalls.Proofs.Sec5.OdometerCentreLowerStability

/-! # Joint spatial and pole stability of clusters away from the pole -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The disc Green function is jointly continuous at distinct interior points. -/
theorem continuousAt_greenFunction_ball_pair {R : ℝ} {z x : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R) (hzx : z ≠ x) :
    ContinuousAt (fun p : ℂ × ℂ => greenFunction (ball 0 R) p.1 p.2) (z, x) := by
  have hR : 0 < R := (norm_nonneg z).trans_lt (mem_ball_zero_iff.mp hz)
  have hnum : ‖(R : ℂ) ^ 2 - starRingEnd ℂ z * x‖ ≠ 0 :=
    (norm_sub_conj_mul_pos hR (mem_ball_zero_iff.mp hz) (mem_ball_zero_iff.mp hx).le).ne'
  have hden : R * ‖z - x‖ ≠ 0 := mul_ne_zero hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzx))
  have hn : ContinuousAt (fun p : ℂ × ℂ => ‖(R : ℂ) ^ 2 - starRingEnd ℂ p.1 * p.2‖) (z, x) := by fun_prop
  have hd : ContinuousAt (fun p : ℂ × ℂ => R * ‖p.1 - p.2‖) (z, x) := by fun_prop
  have hc : ContinuousAt (fun p : ℂ × ℂ => greenBall R p.1 p.2) (z, x) := by
    show ContinuousAt (fun p : ℂ × ℂ => (2 * Real.pi)⁻¹ *
      Real.log (‖(R : ℂ) ^ 2 - starRingEnd ℂ p.1 * p.2‖ / (R * ‖p.1 - p.2‖))) (z, x)
    exact continuousAt_const.mul ((hn.div hd hden).log (div_ne_zero hnum hden))
  apply hc.congr
  filter_upwards [continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds hz),
    continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hx),
    ((isOpen_ne : IsOpen {w : ℂ | w ≠ 0}).preimage
      (continuous_fst.sub continuous_snd)).mem_nhds (sub_ne_zero.mpr hzx)] with p hpz hpx hpne
  exact (greenFunction_ball hpz hpx (sub_ne_zero.mp hpne)).symm

/-- Away from the pole, cluster membership is stable jointly under small
changes of the pole and of the evaluation point. -/
theorem eventually_cluster_mem_pair_of_ne
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {t : ℝ} (ht : 0 < t) {z x : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    (hx : x ∈ cluster μ R z t) (hxz : x ≠ z) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (z, x), p.2 ∈ cluster μ R p.1 t := by
  have hcompat := obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV
  have hnc : x ∈ nonCoincidenceSet μ R z t := by
    rw [← (hcompat z hz t ht).2.2.1]
    exact hx
  have hgap : obstacle μ R z t x < shiftedLeastSupersolution μ R z t x :=
    hnc.2.resolve_left hxz
  let ε := (shiftedLeastSupersolution μ R z t x - obstacle μ R z t x) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hq := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hgreen := continuousAt_greenFunction_ball_pair hz hnc.1 (Ne.symm hxz)
  have hqc : ContinuousAt (greenPotentialBall μ R) x :=
    hq.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hnc.1) ball_subset_closedBall)
  have hpot : ContinuousAt (fun p : ℂ × ℂ => greenPotentialBall μ R p.2) (z, x) :=
    hqc.comp (f := fun p : ℂ × ℂ => p.2) (g := greenPotentialBall μ R) continuous_snd.continuousAt
  have hobs : ContinuousAt (fun p : ℂ × ℂ => obstacle μ R p.1 t p.2) (z, x) := by
    unfold obstacle
    exact (continuousAt_const.mul hgreen).add hpot
  have hv : ContinuousAt (shiftedLeastSupersolution μ R z t) x :=
    (obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βm βp hR hV
    z hz t ht).2.1.continuousAt
      (mem_of_superset (isOpen_ball.mem_nhds hnc.1) ball_subset_closedBall)
  have hdiff : ContinuousAt (fun p : ℂ × ℂ =>
      shiftedLeastSupersolution μ R z t p.2 - obstacle μ R p.1 t p.2) (z, x) :=
    (hv.comp (f := fun p : ℂ × ℂ => p.2)
      (g := shiftedLeastSupersolution μ R z t) continuous_snd.continuousAt).sub hobs
  have hpos : ε < shiftedLeastSupersolution μ R z t x - obstacle μ R z t x := by
    dsimp [ε]; linarith
  have htr := eventually_truncatedShiftedObstacle_le_add hR hz ht hq hε
  have hne : ∀ w : ℂ, (shiftedSupersolutions μ R w t).Nonempty := fun w =>
    ⟨greenPotentialBall μ R, greenPotentialBall_mem_shiftedSupersolutions ht.le hq
      (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV).laplacianLE⟩
  have haway : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, x), p.2 ≠ z :=
    continuous_snd.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hxz)
  filter_upwards [continuous_fst.continuousAt.eventually htr,
    continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds hz),
    continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hnc.1),
    hdiff.eventually (isOpen_Ioi.mem_nhds hpos), haway] with p htrp hpz hpx hp hpxz
  have hnonneg : ∀ w ∈ shiftedSupersolutions μ R p.1 t,
      ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y := by
    intro w hw y hy
    exact shiftedSupersolution_nonneg_on_closedBall hμ hR hV hpz ht hw hy
  have hle := shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add
    (c := ε) (hne p.1) hnonneg htrp (ball_subset_closedBall hpx) hpxz
  rw [(hcompat p.1 hpz t ht).2.2.1]
  exact ⟨hpx, Or.inr (by linarith)⟩

/-- A compact subset of the cluster which avoids the pole remains inside
the cluster for every sufficiently nearby pole. -/
theorem eventually_compact_subset_cluster_of_centre
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    {K : Set ℂ} (hK : IsCompact K) (hsub : K ⊆ cluster μ R z t) (hzK : z ∉ K) :
    ∀ᶠ z' in 𝓝 z, K ⊆ cluster μ R z' t := by
  let S : Set (ℂ × ℂ) := {p | p.2 ∈ cluster μ R p.1 t}
  have hprod : S ∈ (𝓝 z) ×ˢ (𝓝ˢ K) := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    rw [← nhds_prod_eq]
    exact eventually_cluster_mem_pair_of_ne hμ hR hV ht hz (hsub hx)
      (fun h => hzK (h ▸ hx))
  obtain ⟨V, hV', W, hW, hVW⟩ := Filter.mem_prod_iff.mp hprod
  filter_upwards [hV'] with z' hz'
  intro x hx
  change (z', x) ∈ S
  exact hVW ⟨hz', mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hW x hx)⟩

universe u

/-- Almost surely, compact subsets away from the pole persist under pole
motion, simultaneously for all radii, positive times and poles. -/
theorem ae_eventually_compact_subset_cluster_of_centre
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z ∈ ball (0 : ℂ) R,
      ∀ K : Set ℂ, IsCompact K → K ⊆ cluster (μ ω) R z t → z ∉ K →
      ∀ᶠ z' in 𝓝 z, K ⊆ cluster (μ ω) R z' t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hv
  intro R t hR ht z hz K hK hsub hzk
  exact eventually_compact_subset_cluster_of_centre hv.1 hR (hv.2 R hR) ht hz hK hsub hzk

end HarmonicBalls
