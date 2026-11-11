import HarmonicBalls.Proofs.Sec11.MassDiameterScaleSelection

/-! # Positive mass thresholds for the mass-diameter construction -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal

/-- A positive-probability event on which a set has positive mass admits a
    deterministic positive threshold on a positive-probability subevent. -/
theorem exists_positive_mass_threshold
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω) (S : Set X)
    (hpos : 0 < P {ω | ω ∈ A ∧ 0 < μ ω S}) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
  let E : ℕ → Set Ω := fun n =>
    {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ < μ ω S}
  have hsub : {ω | ω ∈ A ∧ 0 < μ ω S} ⊆ ⋃ n, E n := by
    intro ω hω
    obtain ⟨n, hn, hmass⟩ := ENNReal.exists_nat_pos_inv_mul_lt
      (a := (8 : ℝ≥0∞)) (b := μ ω S) (by simp) hω.2.ne'
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine mem_iUnion.mpr ⟨m, hω.1, ?_⟩
    simpa [mul_comm, Nat.succ_eq_add_one] using hmass
  have hu : 0 < P (⋃ n, E n) := hpos.trans_le (measure_mono hsub)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hu.ne'
  refine ⟨((n + 1 : ℕ) : ℝ≥0∞)⁻¹, ?_, hn⟩
  exact ENNReal.inv_pos.mpr (by simp)

/-- A positive mass event and a sufficiently small tile-diameter failure
    probability select a positive threshold, one scale, and one of four tile
    classes. -/
theorem exists_positive_mass_scale_and_four_tile_class
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S : Set X) (C : ℕ → Fin 4 → Set X) (E : ℕ → Set Ω)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hpos : 0 < P {ω | ω ∈ A ∧ 0 < μ ω S})
    (hsmall : ∀ c : ℝ≥0∞, 0 < c →
      0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S} →
      ∃ n, P (E n)ᶜ < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ n i,
      0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (2 : ℝ≥0∞) * c < μ ω (C n i)} := by
  obtain ⟨c, hc, hp⟩ := exists_positive_mass_threshold P μ A S hpos
  obtain ⟨n, i, hi⟩ := exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    P μ A S C E c hcover (hsmall c hc hp)
  exact ⟨c, hc, n, i, hi⟩

end HarmonicBalls
