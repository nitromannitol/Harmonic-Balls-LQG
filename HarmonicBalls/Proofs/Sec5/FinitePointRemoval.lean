import HarmonicBalls.Proofs.Sec5.ContinuousPointRemoval

/-! # Removal of finitely many points for continuous supersolutions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- A continuous distributional supersolution on an open set with finitely
many points removed is a supersolution on the whole set. -/
theorem laplacianLE_zero_of_finite_removal {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ → ℝ} (hvc : ContinuousOn v U) (K : Finset ℂ)
    (hv : LaplacianLE v 0 (U \ (K : Set ℂ))) : LaplacianLE v 0 U := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using hv
  | @insert a K ha ih =>
    let V := U \ (K : Set ℂ)
    have hVo : IsOpen V := hU.sdiff K.finite_toSet.isClosed
    have hVc : ContinuousOn v V := hvc.mono sdiff_subset
    have hp : LaplacianLE v 0 (V \ {a}) := by
      convert hv using 1; ext x; simp [V, and_comm, and_assoc]
    by_cases haV : a ∈ V
    · exact ih (laplacianLE_zero_of_punctured hVo haV hVc hp)
    · have hV : V \ {a} = V := by
        ext x
        simp only [mem_sdiff, mem_singleton_iff]
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, fun he => haV (he ▸ hx)⟩
      rw [hV] at hp
      exact ih hp

/-- A continuous function which is superharmonic away from finitely many
points is superharmonic throughout the open domain. -/
theorem isSuperharmonicOn_of_finite_removal {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ → ℝ} (hvc : ContinuousOn v U) (K : Finset ℂ)
    (hv : IsSuperharmonicOn (U \ (K : Set ℂ)) v) : IsSuperharmonicOn U v := by
  have hΔ := laplacianLEOfSuperharmonicStep_holds (U \ (K : Set ℂ)) v
    (hU.sdiff K.finite_toSet.isClosed) (hvc.mono sdiff_subset) hv
  exact superharmonicOfLaplacianLEStep_holds U v hU hvc
    (laplacianLE_zero_of_finite_removal hU hvc K hΔ)

/-- A continuous measure-valued supersolution extends across finitely many
points when the measure admits a continuous potential on the domain. -/
theorem laplacianLE_of_finite_removal {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) {w q : ℂ → ℝ}
    (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (K : Finset ℂ)
    (hw : LaplacianLE w μ (U \ (K : Set ℂ))) : LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_finite_removal hU (hwc.add hqc) K hp)

/-- Under volume growth, continuous measure-valued supersolutions on a disc
extend across finitely many points. -/
theorem laplacianLE_disc_of_finite_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {w : ℂ → ℝ}
    (hwc : ContinuousOn w (ball (0 : ℂ) R)) (K : Finset ℂ)
    (hw : LaplacianLE w μ (ball (0 : ℂ) R \ (K : Set ℂ))) :
    LaplacianLE w μ (ball 0 R) := by
  exact laplacianLE_of_finite_removal hμ isOpen_ball hwc
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) K hw


end HarmonicBalls
