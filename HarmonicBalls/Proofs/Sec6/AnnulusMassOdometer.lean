import HarmonicBalls.Proofs.Sec6.DiscMassOdometer

/-! # Annular mass and truncated odometers

A scale-independent finite cover and the disc comparison yield the mass
estimate at a point of the outer annulus.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

universe u

/-- The mass in a middle annulus is controlled uniformly by the truncated
odometer at some point in the outer annulus. -/
theorem exists_annulus_mass_le_truncated_odometer
    {s₁ s₂ s₃ s₄ : ℝ} (h12 : s₁ < s₂) (h23 : s₂ < s₃)
    (h34 : s₃ < s₄) (hs₂ : 0 ≤ s₂) :
    ∃ N : ℕ, ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {R βminus βplus : ℝ}, 0 < R → VolumeGrowth μ R βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) R → ∀ {t : ℝ}, 0 < t →
      ∀ {w : ℂ} {r : ℝ}, 0 < r →
      annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) R \ {z} →
      ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster μ R z t →
      (∀ x ∈ Λ, connectedComponentIn
        (annulus w (s₁ * r) (s₄ * r) ∩ cluster μ R z t) x ⊆ Λ) →
      ∃ y ∈ annulus w (s₁ * r) (s₄ * r),
        ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) *
          (μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ)).toReal ≤
          (N : ℝ) * Λ.indicator (odometer μ R z t) y := by
  obtain ⟨δ, hδ, T, _, hcover⟩ := exists_uniform_annulus_mass_disc h12 h23 h34 hs₂
  refine ⟨T.card, ?_⟩
  intro μ hμ R βminus βplus hR hV z hz t ht w r hr hUsub Λ hΛsub hcomp
  obtain ⟨x, _, _, hdisc, hmass⟩ := hcover w r hr μ Λ
  have hUopen : IsOpen (annulus w (s₁ * r) (s₄ * r)) :=
    isOpen_ball.sdiff isClosed_closedBall
  have hd : 0 < δ * r := mul_pos hδ hr
  have hdisc' : closedBall (r • x + w) (2 * (δ * r)) ⊆
      annulus w (s₁ * r) (s₄ * r) := by
    convert hdisc using 1; ring
  obtain ⟨y, hy, hbound⟩ := mass_le_truncated_odometer_of_disc
    hμ hR hV hz ht hUopen hUsub hΛsub hcomp hd hdisc' hmass
  exact ⟨y, hdisc' (sphere_subset_closedBall hy), hbound⟩

/-- The deterministic annulus mass estimate for a locally finite measure
with volume growth in the unit disc. -/
theorem annulus_mass_le_odometer_of_volumeGrowth
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {w : ℂ} {r : ℝ}, 0 < r →
      annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) 1 \ {z} →
      ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t →
      (∀ x ∈ Λ, connectedComponentIn
        (annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t) x ⊆ Λ) →
      μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≤
        ENNReal.ofReal C * ⨆ x ∈ Λ, odometerExt μ z t x := by
  classical
  obtain ⟨N, hN⟩ := exists_annulus_mass_le_truncated_odometer h12 h23 h34 (by linarith)
  let K : ℝ := (2 * Real.pi)⁻¹ * Real.log (3 / 2)
  have hK : 0 < K := log_three_halves_green_constant_pos
  let C : ℝ := ((N : ℝ) + 1) / K
  have hC : 0 < C := div_pos (by positivity) hK
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht w r hr hUsub Λ hΛsub hcomp
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨y, hy, hbound⟩ := hN hμ (by norm_num : (0 : ℝ) < 1) hV hz ht hr hUsub Λ hΛsub hcomp
  have hfinite : μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (show annulus w (s₂ * r) (s₃ * r) ∩ Λ ⊆ ball (0 : ℂ) 1 from
      fun x hx => (hUsub (hΛsub hx.2).1).1)).trans_lt (measure_ball_lt_top (μ := μ))
  have hv0 : 0 ≤ Λ.indicator (odometer μ 1 z t) y := by
    by_cases hyΛ : y ∈ Λ
    · simpa only [indicator_of_mem hyΛ] using odometer_nonneg ht.le
        (ball_subset_closedBall (hUsub hy).1) (hUsub hy).2
    · simp [hyΛ]
  have hreal : (μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ)).toReal ≤
      C * Λ.indicator (odometer μ 1 z t) y := by
    have hCeq : K * C = (N : ℝ) + 1 := by
      dsimp only [C]
      field_simp
    have hprod := mul_le_mul_of_nonneg_right
      (show (N : ℝ) ≤ K * C by rw [hCeq]; linarith) hv0
    apply le_of_mul_le_mul_left _ hK
    nlinarith [hbound, hprod]
  have hindicator : ENNReal.ofReal (Λ.indicator (odometer μ 1 z t) y) ≤
      ⨆ x ∈ Λ, odometerExt μ z t x := by
    by_cases hyΛ : y ∈ Λ
    · have hyz : y ≠ z := by simpa only [mem_singleton_iff] using (hUsub hy).2
      simpa only [indicator_of_mem hyΛ, odometerExt, hyz, ↓reduceIte] using
        (le_iSup_of_le y (le_iSup_of_le hyΛ le_rfl) :
          odometerExt μ z t y ≤ ⨆ x ∈ Λ, odometerExt μ z t x)
    · simp [hyΛ]
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_toReal hfinite, ENNReal.ofReal_mul hC.le] at hh
  exact hh.trans (by gcongr)

/-- Lemma 6.8 follows from the all-scales LQG volume-growth statement. -/
theorem annulusMassBoundByOdometer_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : AnnulusMassBoundByOdometerStmt.{u} := by
  intro s₁ s₂ s₃ s₄ hs₁ h12 h23 h34
  obtain ⟨C, hC, hdet⟩ := annulus_mass_le_odometer_of_volumeGrowth hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro z hz t ht r hr w hsub hznot Λ hΛsub hcomp
  have hUsub : annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) 1 \ {z} := by
    intro x hx
    refine ⟨hsub hx, ?_⟩
    intro hxz
    exact hznot (by simpa only [mem_singleton_iff] using hxz ▸ hx)
  exact hdet hω.1 (hω.2 1 (by norm_num)) hz ht hr hUsub Λ hΛsub hcomp

end HarmonicBalls.Section6
