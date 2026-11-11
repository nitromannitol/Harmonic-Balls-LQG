import HarmonicBalls.Proofs.Sec5.PuncturedSubharmonicMaximum
import HarmonicBalls.Proofs.Sec5.PuncturePotentialShift
import HarmonicBalls.Proofs.Sec4.Sweep
import HarmonicBalls.Proofs.SecA.Basic

/-! # Removal of a point for continuous superharmonic functions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology InnerProductSpace Laplacian

/-- A continuous superharmonic function on an open set with one point removed
is superharmonic on the whole set. -/
theorem isSuperharmonicOn_of_punctured {U : Set ℂ} {a : ℂ} {v : ℂ → ℝ}
    (hU : IsOpen U) (ha : a ∈ U) (hvc : ContinuousOn v U)
    (hs : IsSuperharmonicOn (U \ {a}) v) : IsSuperharmonicOn U v := by
  have hlocal : HasLocalSuperMean U v := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU a ha
      refine ⟨δ / 2, half_pos hδ, fun r hr => ?_⟩
      have hr0 : 0 < r := hr.1
      have hball : closedBall a r ⊆ U :=
        (closedBall_subset_ball (lt_trans hr.2 (half_lt_self hδ))).trans hδU
      have hD : IsSweepDisc U a r := ⟨hr0, hball⟩
      have hvi : CircleIntegrable v a r := hD.circleIntegrable hvc
      let p := discSweep U a r v
      have hpc : ContinuousOn p U := continuousOn_discSweep hU hvc
      have hp : HarmonicOnNhd p (ball a r) := by
        intro y hy
        apply (harmonicAt_congr_nhds (f₁ := discPoissonIntegral v a r) (f₂ := p) ?_).mp
          (harmonicOnNhd_discPoissonIntegral hvi y hy)
        filter_upwards [isOpen_ball.mem_nhds hy] with z hz
        exact (discSweep_of_mem hD hz).symm
      let D := ball a r \ {a}
      have hDU : D ⊆ U \ {a} := fun _ hy => ⟨hball (ball_subset_closedBall hy.1), hy.2⟩
      have hsD : IsSuperharmonicOn D v :=
        ⟨hs.1.mono hDU, fun y hy s hsr hsb => hs.2 y (hDU hy) s hsr (hsb.trans hDU)⟩
      have hneg : IsSubharmonicOn D (-v) := by simpa [IsSubharmonicOn] using hsD
      have hf : ContinuousOn (-v) D := (hvc.mono (hDU.trans sdiff_subset)).neg
      have hsub := hneg.add_harmonicOnNhd hf (hp.mono sdiff_subset)
      have hcomp := isSubharmonicOn_punctured_ball_le_of_continuousOn
        (mem_ball_self hr0) (((hvc.neg).add hpc).mono hball) hsub (C := 0) (by
          intro y hy
          have hyb : y ∉ ball a r := by
            rw [mem_ball, mem_sphere] at *
            linarith
          change -v y + discSweep U a r v y ≤ 0
          rw [discSweep_of_not (fun h => hyb h.2)]
          simp) a (mem_closedBall_self hr0.le)
      have heq := discSweep_of_mem (f := v) hD (mem_ball_self hr0)
      change -v a + p a ≤ 0 at hcomp
      dsimp [p] at hcomp
      rw [heq, discPoissonIntegral_center hr0.ne'] at hcomp
      exact ⟨hvi, by linarith⟩
    · have hxD : x ∈ U \ {a} := ⟨hx, by simpa using hxa⟩
      have hopen : IsOpen (U \ {a}) := hU.sdiff isClosed_singleton
      obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.mp hopen x hxD
      refine ⟨δ, hδ, fun r hr => ?_⟩
      exact hs.2 x hxD r hr.1 ((closedBall_subset_ball hr.2).trans hδD)
  refine ⟨hvc.lowerSemicontinuousOn, fun x hx r hr hball => ?_⟩
  have hi : CircleIntegrable v x r :=
    (hvc.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le
  exact ⟨hi, circleAverage_le_of_localSuperMean hvc.lowerSemicontinuousOn hlocal hr hball hi⟩

/-- A continuous distributional supersolution extends across a point. -/
theorem laplacianLE_zero_of_punctured {U : Set ℂ} {a : ℂ} {v : ℂ → ℝ}
    (hU : IsOpen U) (ha : a ∈ U) (hvc : ContinuousOn v U)
    (hv : LaplacianLE v 0 (U \ {a})) : LaplacianLE v 0 U := by
  have hs := superharmonicOfLaplacianLEStep_holds _ _ (hU.sdiff isClosed_singleton)
    (hvc.mono sdiff_subset) hv
  exact laplacianLEOfSuperharmonicStep_holds U v hU hvc
    (isSuperharmonicOn_of_punctured hU ha hvc hs)

/-- Under volume growth the measure-valued Laplacian bound also extends
across the puncture. -/
theorem laplacianLE_punctured_disc {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βm βp : ℝ} {a : ℂ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) {w : ℂ → ℝ}
    (hwc : ContinuousOn w (ball (0 : ℂ) R))
    (hw : LaplacianLE w μ (ball (0 : ℂ) R \ {a})) :
    LaplacianLE w μ (ball 0 R) := by
  exact laplacianLE_punctured_disc_of_zero_point_removal hμ hR hV
    (fun _ hv hvΔ => laplacianLE_zero_of_punctured isOpen_ball ha hv hvΔ) hwc hw

/-- The punctured-disc and disc least supersolutions agree away from the
puncture and the pole. -/
theorem leastSupersolutionOn_punctured_disc_eq {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hx : x ∈ ball (0 : ℂ) R \ {a}) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x =
      leastSupersolution μ R z t x := by
  apply leastSupersolutionOn_punctured_disc_eq_of_point_removal hμ hR hV ha hz ht hx hxz
  intro w hw
  exact laplacianLE_punctured_disc hμ hR hV ha
    (hw.1.mono (by rw [closure_punctured_disc ha]; exact ball_subset_closedBall)) hw.2.1

/-- Removing a point deletes exactly that point from the disc cluster. -/
theorem clusterOn_punctured_disc_eq_sdiff {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βm βp t : ℝ} {z a : ℂ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t) :
    clusterOn μ (ball (0 : ℂ) R \ {a}) z t = cluster μ R z t \ {a} := by
  exact clusterOn_punctured_disc_eq_sdiff_of_zero_point_removal hμ hR hV ha hz ht
    (fun _ hv hvΔ => laplacianLE_zero_of_punctured isOpen_ball ha hv hvΔ)


end HarmonicBalls
