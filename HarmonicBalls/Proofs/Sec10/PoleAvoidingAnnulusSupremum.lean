import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusMass

/-! # Annulus mass bounded by the odometer supremum

The finite-cover estimate gives the usual extended-nonnegative-real form of
Lemma 6.8 for a union of annular components that avoids the pole.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6
open scoped ENNReal

/-- Under volume growth and restricted disc-potential regularity, the mass in
the middle annulus is bounded by the odometer supremum on any union of outer
annulus components avoiding the pole. -/
theorem annulus_mass_le_odometer_of_pole_not_mem_of_potential_regular
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {w : ℂ} {r : ℝ}, 0 < r →
      annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) 1 →
      ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t →
      (∀ x ∈ Λ, connectedComponentIn
        (annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t) x ⊆ Λ) →
      z ∉ Λ →
      (∀ c : ℂ, closedBall c (2 * (δ * r)) ⊆ annulus w (s₁ * r) (s₄ * r) →
        ContinuousOn (fun x => ∫ y in ball c (2 * (δ * r)) ∩ Λ,
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) (closedBall c (2 * (δ * r))) ∧
        HasLaplacian (fun x => ∫ y in ball c (2 * (δ * r)) ∩ Λ,
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) 0
          (μ.restrict (ball c (2 * (δ * r)) ∩ Λ)) (ball c (2 * (δ * r)))) →
      μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≤
        ENNReal.ofReal C * ⨆ x ∈ Λ, odometerExt μ z t x := by
  classical
  obtain ⟨δ, hδ, T, hT, hN⟩ :=
    exists_annulus_mass_le_truncated_odometer_of_potential_regular h12 h23 h34 (by linarith)
  let K : ℝ := (2 * Real.pi)⁻¹ * Real.log (3 / 2)
  have hK : 0 < K := log_three_halves_green_constant_pos
  let C : ℝ := ((T.card : ℝ) + 1) / K
  have hC : 0 < C := div_pos (by positivity) hK
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht w r hr hUsub Λ hΛsub hcomp hzΛ hregular
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨y, hy, hbound⟩ := hN hμ (by norm_num : (0 : ℝ) < 1) hV hz ht hr
    hUsub hΛsub hcomp hzΛ hregular
  have hfinite : μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (show annulus w (s₂ * r) (s₃ * r) ∩ Λ ⊆ ball (0 : ℂ) 1 from
      fun x hx => hUsub (hΛsub hx.2).1)).trans_lt (measure_ball_lt_top (μ := μ))
  have hv0 : 0 ≤ Λ.indicator (odometer μ 1 z t) y := by
    by_cases hyΛ : y ∈ Λ
    · have hyz : y ≠ z := by intro h; subst y; exact hzΛ hyΛ
      simpa only [indicator_of_mem hyΛ] using odometer_nonneg ht.le
        (ball_subset_closedBall (hUsub hy)) (by simpa using hyz)
    · simp [hyΛ]
  have hreal : (μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ)).toReal ≤
      C * Λ.indicator (odometer μ 1 z t) y := by
    have hCeq : K * C = (T.card : ℝ) + 1 := by
      dsimp only [C]
      field_simp
    have hprod := mul_le_mul_of_nonneg_right
      (show (T.card : ℝ) ≤ K * C by rw [hCeq]; linarith) hv0
    apply le_of_mul_le_mul_left _ hK
    nlinarith [hbound, hprod]
  have hindicator : ENNReal.ofReal (Λ.indicator (odometer μ 1 z t) y) ≤
      ⨆ x ∈ Λ, odometerExt μ z t x := by
    by_cases hyΛ : y ∈ Λ
    · have hyz : y ≠ z := by intro h; subst y; exact hzΛ hyΛ
      simpa only [indicator_of_mem hyΛ, odometerExt, hyz, ↓reduceIte] using
        (le_iSup_of_le y (le_iSup_of_le hyΛ le_rfl) :
          odometerExt μ z t y ≤ ⨆ x ∈ Λ, odometerExt μ z t x)
    · simp [hyΛ]
  have hh := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_toReal hfinite, ENNReal.ofReal_mul hC.le] at hh
  exact hh.trans (by gcongr)

end HarmonicBalls
