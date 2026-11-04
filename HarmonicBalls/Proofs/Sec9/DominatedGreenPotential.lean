import HarmonicBalls.Proofs.Sec4.GreenRepresentation

/-!
# Green potential of a dominated measure

A measure dominated by one with volume growth has a continuous Green potential with the
expected distributional Laplacian. This isolates the argument used in the Green representation
proof for use with the restriction of the LQG measure to a subharmonic ball.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- A dominated measure has a continuous Green potential and the expected Laplacian on the disc. -/
theorem dominated_greenPotentialBall {μ σ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hσ : σ ≤ μ) :
    ContinuousOn (greenPotentialBall (σ.restrict (ball 0 R)) R) (closedBall 0 R) ∧
    HasLaplacian (greenPotentialBall (σ.restrict (ball 0 R)) R) 0 (σ.restrict (ball 0 R))
      (ball 0 R) := by
  set B := ball (0 : ℂ) R with hB
  have hBm : MeasurableSet B := measurableSet_ball
  set σ' := σ.restrict B with hσ'
  have hσ'μ : σ' ≤ μ := Measure.restrict_le_self.trans hσ
  have hV' : VolumeGrowth (σ' + μ) R βm (βp / 2) := hV.add_of_le hσ'μ
  have hσμ' : σ' ≤ σ' + μ := Measure.le_add_right le_rfl
  have : IsLocallyFiniteMeasure σ' := Measure.isLocallyFiniteMeasure_of_le hσ'μ
  have hsumlf : IsLocallyFiniteMeasure (σ' + μ) := ⟨fun x => by
    obtain ⟨s, hs, hμs⟩ := μ.finiteAt_nhds x
    refine ⟨s, hs, ?_⟩
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨(Measure.le_iff'.1 hσ'μ s).trans_lt hμs, hμs⟩⟩
  have hint : ∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => greenFunction B y x) (σ'.restrict B) :=
    fun x hx => (integrable_greenFunction_ball_left hR hV' hx).mono_measure
      (Measure.restrict_mono subset_rfl hσμ')
  have hsplit : ∀ x ∈ closedBall (0 : ℂ) R,
      greenPotentialBall (σ' + μ) R x = greenPotentialBall σ' R x + greenPotentialBall μ R x := by
    intro x hx
    simp only [greenPotentialBall]
    rw [Measure.restrict_add, integral_add_measure (hint x hx) (integrable_greenFunction_ball_left hR hV hx)]
  have hΔsum := greenPotentialBallLaplacianStep_holds (σ' + μ) hsumlf R βm (βp / 2) hR hV'
  have hΔμ := greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV
  have hcsum := greenPotentialBallContinuousStep_holds (σ' + μ) hsumlf R βm (βp / 2) hR hV'
  have hcμ := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hpeq : EqOn (fun x => greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x)
      (greenPotentialBall σ' R) (closedBall 0 R) := fun x hx => by
    simp only [hsplit x hx]
    ring
  refine ⟨(hcsum.sub hcμ).congr fun x hx => (hpeq hx).symm, ?_⟩
  have hd : HasLaplacian (fun x => greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x) 0 σ' B := by
    refine ⟨hΔsum.1.sub hΔμ.1, fun φ hφ => ?_⟩
    obtain ⟨-, hi1, e1⟩ := hΔsum.2 φ hφ
    obtain ⟨-, hiμ, e2⟩ := hΔμ.2 φ hφ
    refine ⟨integrable_zero_measure, hi1.mono_measure hσμ', ?_⟩
    have hfun : (fun x => (greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x) * Δ φ x) =
        fun x => greenPotentialBall (σ' + μ) R x * Δ φ x - greenPotentialBall μ R x * Δ φ x := by
      funext x
      ring
    rw [hfun, integral_sub (integrable_mul_laplacian hΔsum.1 hφ) (integrable_mul_laplacian hΔμ.1 hφ), e1, e2,
      integral_add_measure (hi1.mono_measure hσμ') hiμ]
    simp only [integral_zero_measure]
    ring
  exact hd.congr_eqOn hBm (hpeq.mono ball_subset_closedBall)

end HarmonicBalls
