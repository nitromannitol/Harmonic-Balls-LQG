import HarmonicBalls.Proofs.Sec6.AnnulusOdometerBound
import HarmonicBalls.Proofs.Sec6.AnnulusMassOdometer

/-! # Lemma 6.10 from LQG volume growth -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

universe u

/-- The frozen Lemma 6.10 follows from all-scales LQG volume growth. -/
theorem odometerBoundByAnnulusMass_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : OdometerBoundByAnnulusMassStmt.{u} := by
  intro s₁ s₂ s₃ s₄ hs₁ h12 h23 h34
  obtain ⟨C, hC, hdet⟩ := exists_odometer_bound_by_annulusGreenPotentialSup hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro z hz t ht ρ hρ c hA hnot
  have hsub : annulus c (s₂ * ρ) (s₃ * ρ) ⊆ annulus c (s₁ * ρ) (s₄ * ρ) :=
    annulus_subset_annulus (mul_le_mul_of_nonneg_right h12.le hρ.le)
      (mul_le_mul_of_nonneg_right h34.le hρ.le)
  have heq : (⨆ x ∈ annulus c (s₂ * ρ) (s₃ * ρ), odometerExt (μ ω) z t x) =
      ⨆ x ∈ annulus c (s₂ * ρ) (s₃ * ρ), ENNReal.ofReal (odometer (μ ω) 1 z t x) := by
    apply iSup_congr
    intro x
    apply iSup_congr
    intro hx
    have hxz : x ≠ z := by simpa using (hA (hsub hx)).2
    simp [odometerExt, hxz]
  rw [heq]
  exact hdet (μ ω) hω.1 1 βm βp (by norm_num) (hω.2 1 (by norm_num)) z hz t ht ρ hρ c hA hnot

end HarmonicBalls.Section6
