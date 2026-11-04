import HarmonicBalls.Proofs.Sec10.PoleAvoidingHarnackAnchor
import HarmonicBalls.Proofs.Sec6.AnnulusHarnack

/-! # Harnack bounds for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A point outside the component anchors a uniform annular Harnack estimate. -/
theorem exists_pole_avoiding_component_annulus_odometer_bound
    {s₁ s₂ s₃ s₄ : ℝ} (h1 : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {c : ℂ}, annulus c (s₁ * ρ) (s₄ * ρ) ⊆ U →
      (annulus c (s₂ * ρ) (s₃ * ρ) \ D).Nonempty →
      ⨆ x ∈ annulus c (s₂ * ρ) (s₃ * ρ) ∩ D, odometerExt μ z t x ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ c (s₁ * ρ) (s₄ * ρ) := by
  classical
  obtain ⟨C, hC, hH⟩ := exists_uniform_annulus_harnack h1 h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD ρ hρ c hA hanchor
  obtain ⟨y, hy, hyD⟩ := hanchor
  have hmid : annulus c (s₂ * ρ) (s₃ * ρ) ⊆ annulus c (s₁ * ρ) (s₄ * ρ) :=
    annulus_subset_annulus (mul_le_mul_of_nonneg_right h12.le hρ.le)
      (mul_le_mul_of_nonneg_right h34.le hρ.le)
  obtain ⟨a₀, ha₀, hDa⟩ := hD
  have hDsub : D ⊆ U ∩ cluster μ 1 z t := by
    rw [← hDa]
    exact connectedComponentIn_subset _ _
  have hcomp : ∀ x ∈ D, connectedComponentIn (U ∩ cluster μ 1 z t) x ⊆ D := by
    intro x hx
    rw [← hDa] at hx ⊢
    exact (connectedComponentIn_eq hx).symm.subset
  obtain ⟨hLsub, hLcomp⟩ := inter_union_components_of_subset hA hDsub hcomp
  obtain ⟨q, _, hq0, hqbound, hsum0, hharm⟩ :=
    exists_pole_avoiding_annulus_classical_harmonic_correction hμ (by norm_num) hV hz ht
      (mul_lt_mul_of_pos_right (lt_trans h12 (lt_trans h23 h34)) hρ)
      (mul_pos (lt_trans h1 (lt_trans h12 (lt_trans h23 h34))) hρ)
      (hA.trans hUsub) hLsub hLcomp (fun h => hzD h.2)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  have hxL : x ∈ annulus c (s₁ * ρ) (s₄ * ρ) ∩ D := ⟨hmid hx.1, hx.2⟩
  have hyL : y ∉ annulus c (s₁ * ρ) (s₄ * ρ) ∩ D := fun h => hyD h.2
  have hcmp := hH ρ hρ c _ hharm hsum0 x hx.1 y hy
  simp only [indicator_of_mem hxL, indicator_of_notMem hyL, zero_add] at hcmp
  have hle : odometer μ 1 z t x ≤ C * q y := by
    have := hq0 x
    linarith
  have hxz : x ≠ z := fun h => hzD (h ▸ hx.2)
  simp only [odometerExt, hxz, ↓reduceIte]
  calc
    ENNReal.ofReal (odometer μ 1 z t x) ≤ ENNReal.ofReal (C * q y) :=
      ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal C * ENNReal.ofReal (q y) := ENNReal.ofReal_mul hC.le
    _ ≤ ENNReal.ofReal C * annulusGreenPotentialSup μ c (s₁ * ρ) (s₄ * ρ) :=
      by simpa only [mul_comm] using mul_le_mul_left (hqbound y (hmid hy)) (ENNReal.ofReal C)

/-- Small outer-annulus mass yields the anchor and the component bound, with a
constant independent of the measure, component, center and scale. -/
theorem exists_component_middle_annulus_odometer_bound_of_outer_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, annulus x₀ (ρ / 4) ρ ⊆ U →
      ∀ {C₁m C₁p α : ℝ}, 0 < C₁m → 0 ≤ α →
      annulusBallMassSize μ βminus ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      μ (D ∩ annulus x₀ (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      α < C₁m * (8 : ℝ) ^ (-βminus) →
      ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, odometerExt μ z t x ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ x₀ (ρ / 4) ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_pole_avoiding_component_annulus_odometer_bound
    (s₁ := 1 / 4) (s₂ := 1 / 2) (s₃ := 7 / 8) (s₄ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD ρ hρ x₀ hA C₁m C₁p α h1m hα0 hv1 hmass hα
  have hanchor := exists_middle_annulus_not_mem_of_outer_mass hρ h1m hα0 hv1 hmass hα
  have hbound' := hbound hμ hV hz ht hUsub hD hzD hρ
    (by simpa [div_eq_mul_inv, mul_comm] using hA)
    (by simpa [div_eq_mul_inv, mul_comm] using hanchor)
  simpa [div_eq_mul_inv, mul_comm] using hbound'

end HarmonicBalls
