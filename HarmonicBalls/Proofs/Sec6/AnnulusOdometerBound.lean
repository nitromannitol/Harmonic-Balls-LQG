import HarmonicBalls.Proofs.Sec6.AnnulusHarnack
import HarmonicBalls.Proofs.Sec6.HarnackChain

/-! # Odometer bound by the annular Green potential

The deterministic comparison in Lemma 6.10 follows from the positive
harmonic correction and the scale-uniform planar Harnack inequality.
-/

namespace HarmonicBalls.Section6

open Metric Set

/-- Deterministic form of Lemma 6.10, under volume growth and local finiteness
of the measure. -/
theorem exists_odometer_bound_by_annulusGreenPotentialSup {s₁ s₂ s₃ s₄ : ℝ}
    (h1 : 0 < s₁) (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : MeasureTheory.Measure ℂ), MeasureTheory.IsLocallyFiniteMeasure μ →
      ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
      ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ c : ℂ,
      annulus c (s₁ * ρ) (s₄ * ρ) ⊆ ball 0 R \ {z} →
      ((cluster μ R z t)ᶜ ∩ annulus c (s₂ * ρ) (s₃ * ρ)).Nonempty →
      ⨆ x ∈ annulus c (s₂ * ρ) (s₃ * ρ), ENNReal.ofReal (odometer μ R z t x) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ c (s₁ * ρ) (s₄ * ρ) := by
  obtain ⟨C, hC, harnack⟩ := exists_uniform_annulus_harnack h1 h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro μ hμ R βminus βplus hR hV z hz t ht ρ hρ c hA hnot
  have hs14 : s₁ * ρ < s₄ * ρ := mul_lt_mul_of_pos_right (lt_trans h12 (lt_trans h23 h34)) hρ
  have hs4 : 0 < s₄ * ρ := mul_pos (lt_trans h1 (lt_trans h12 (lt_trans h23 h34))) hρ
  obtain ⟨q, _, hq0, hqbound, hsum0, hharm⟩ :=
    exists_annulus_odometer_classical_harmonic_correction hμ hR hV hz ht hs14 hs4 hA
  have hsub : annulus c (s₂ * ρ) (s₃ * ρ) ⊆ annulus c (s₁ * ρ) (s₄ * ρ) :=
    annulus_subset_annulus (mul_le_mul_of_nonneg_right h12.le hρ.le)
      (mul_le_mul_of_nonneg_right h34.le hρ.le)
  obtain ⟨y, hynot, hy⟩ := hnot
  have hzero := odometer_eq_zero_of_not_mem_cluster_in_annulus ht hA (hsub hy) hynot
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hcmp := harnack ρ hρ c (fun w => odometer μ R z t w + q w) hharm hsum0 x hx y hy
  have hle : odometer μ R z t x ≤ C * q y := by
    rw [hzero, zero_add] at hcmp
    have := hq0 x
    linarith
  calc
    ENNReal.ofReal (odometer μ R z t x) ≤ ENNReal.ofReal (C * q y) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal C * ENNReal.ofReal (q y) := ENNReal.ofReal_mul hC.le
    _ ≤ ENNReal.ofReal C * annulusGreenPotentialSup μ c (s₁ * ρ) (s₄ * ρ) := by
      simpa only [mul_comm] using (mul_le_mul_left (hqbound y (hsub hy)) (ENNReal.ofReal C))

end HarmonicBalls.Section6
