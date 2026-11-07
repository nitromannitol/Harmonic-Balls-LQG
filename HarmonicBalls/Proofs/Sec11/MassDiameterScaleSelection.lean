import HarmonicBalls.Proofs.Sec11.MassDiameterClassSelection

/-! # Selecting the scale and parity class for mass-diameter gluing -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- If the tile diameter event eventually holds almost surely, a positive
    large-mass event selects one deterministic scale and one deterministic
    member of a four-class cover on which the corresponding mass is large.
    No independence or event measurability is assumed. -/
theorem exists_positive_measure_scale_and_four_tile_class
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S : Set X) (C : ℕ → Fin 4 → Set X) (E : ℕ → Set Ω) (c : ℝ≥0∞)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hA : 0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S})
    (hsmall : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∈ E n) :
    ∃ n i, 0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (2 : ℝ≥0∞) * c < μ ω (C n i)} := by
  let B : Set Ω := {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}
  let G : Set Ω := {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n}
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hsmall] with ω hω
    simp only [mem_inter_iff, G, mem_ofPred_eq, hω, and_true]
  have hp : 0 < P (B ∩ G) := by rwa [← measure_congr heq]
  have hsub : B ∩ G ⊆ ⋃ n, B ∩ E n := by
    intro ω hω
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hω.2
    exact mem_iUnion.mpr ⟨n, hω.1, hn n le_rfl⟩
  have hu : 0 < P (⋃ n, B ∩ E n) := hp.trans_le (measure_mono hsub)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hu.ne'
  have hn' : 0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    apply hn.trans_le (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1.1, hω.2, hω.1.2⟩
  obtain ⟨i, hi⟩ := exists_positive_measure_four_tile_class P μ
    {ω | ω ∈ A ∧ ω ∈ E n} S (C n) c (hcover n) (by simpa [and_assoc] using hn')
  exact ⟨n, i, by simpa [and_assoc] using hi⟩

/-- The same scale selection needs only one failure probability smaller than
    the large-mass event. This is the form supplied by convergence in
    probability, without an almost-sure convergence assumption. -/
theorem exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S : Set X) (C : ℕ → Fin 4 → Set X) (E : ℕ → Set Ω) (c : ℝ≥0∞)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hsmall : ∃ n, P (E n)ᶜ < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}) :
    ∃ n i, 0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (2 : ℝ≥0∞) * c < μ ω (C n i)} := by
  obtain ⟨n, hn⟩ := hsmall
  let B : Set Ω := {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}
  have hp : 0 < P (B ∩ E n) := by
    by_contra h
    have hz : P (B ∩ E n) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp h)
    have hle : P B ≤ P (E n)ᶜ := by
      calc
        P B ≤ P ((B ∩ E n) ∪ (E n)ᶜ) := measure_mono (by
          intro ω hω
          by_cases he : ω ∈ E n
          · exact Or.inl ⟨hω, he⟩
          · exact Or.inr he)
        _ ≤ P (B ∩ E n) + P (E n)ᶜ := measure_union_le _ _
        _ = P (E n)ᶜ := by rw [hz, zero_add]
    exact (not_lt_of_ge hle) hn
  have hp' : 0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    apply hp.trans_le (measure_mono ?_)
    intro ω hω
    exact ⟨hω.1.1, hω.2, hω.1.2⟩
  obtain ⟨i, hi⟩ := exists_positive_measure_four_tile_class P μ
    {ω | ω ∈ A ∧ ω ∈ E n} S (C n) c (hcover n) (by simpa [and_assoc] using hp')
  exact ⟨n, i, by simpa [and_assoc] using hi⟩

#print axioms exists_positive_measure_scale_and_four_tile_class_of_failure_bound
#print axioms exists_positive_measure_scale_and_four_tile_class
end HarmonicBalls
