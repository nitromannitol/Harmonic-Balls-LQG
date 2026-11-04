import HarmonicBalls.Steps.Sec11.TimeMeasurable

/-! # Distribution of positive first-entry times -/

namespace HarmonicBalls

open MeasureTheory Set Filter
open scoped ENNReal

/-- If an increasing open family has mass `t` and covers almost every point, the
measure of the strict first-entry sublevel set at any positive time `a` is
`a`. This proves the distribution-function calculation needed in G37. -/
theorem measure_positive_entry_time_preimage_Iio_of_ae_cover
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (Λ : ℝ → Set X)
    (hcover : ∀ᵐ x ∂μ, ∃ t, 0 < t ∧ x ∈ Λ t)
    (hmono : MonotoneOn Λ (Ioi (0 : ℝ)))
    (hmass : ∀ t, 0 < t → μ (Λ t) = ENNReal.ofReal t)
    (a : ℝ) (ha : 0 < a) :
    μ ((fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⁻¹' Iio a) = ENNReal.ofReal a := by
  let E : Set X := (fun x => sInf {t : ℝ | 0 < t ∧ x ∈ Λ t}) ⁻¹' Iio a
  have hE : μ E = μ (⋃ t ∈ Ioo (0 : ℝ) a, Λ t) := by
    apply measure_congr
    filter_upwards [hcover] with x hx
    simp only [E, mem_preimage, mem_Iio, mem_iUnion, mem_Ioo]
    apply propext
    rw [csInf_lt_iff (s := {t : ℝ | 0 < t ∧ x ∈ Λ t})
      ⟨0, fun _ ht => ht.1.le⟩ hx]
    constructor
    · rintro ⟨t, ⟨ht, hxt⟩, hta⟩
      exact ⟨t, ⟨ht, hta⟩, hxt⟩
    · rintro ⟨t, ⟨ht, hta⟩, hxt⟩
      exact ⟨t, ⟨ht, hxt⟩, hta⟩
  have hupper : μ E ≤ ENNReal.ofReal a := by
    rw [← hmass a ha]
    rw [hE]
    apply measure_mono
    intro x hx
    simp only [mem_iUnion, mem_Ioo] at hx
    obtain ⟨t, ⟨ht, hta⟩, hx⟩ := hx
    exact hmono ht ha hta.le hx
  have hfinite : μ E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlower : ∀ t : ℝ, 0 < t → t < a → ENNReal.ofReal t ≤ μ E := by
    intro t ht hta
    rw [← hmass t ht]
    rw [hE]
    apply measure_mono
    intro x hx
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨⟨ht, hta⟩, hx⟩⟩
  have hreal : a ≤ (μ E).toReal := by
    by_contra hn
    have hlt : (μ E).toReal < a := lt_of_not_ge hn
    let t : ℝ := ((μ E).toReal + a) / 2
    have ht : 0 < t := by dsimp [t]; have := ENNReal.toReal_nonneg (a := μ E); linarith
    have hta : t < a := by dsimp [t]; linarith
    have hle : t ≤ (μ E).toReal := (ENNReal.ofReal_le_iff_le_toReal hfinite).1 (hlower t ht hta)
    dsimp [t] at hle
    linarith
  apply le_antisymm hupper
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

end HarmonicBalls
