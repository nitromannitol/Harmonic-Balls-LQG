import HarmonicBalls.Proofs.Sec6.ScaledSingularPhaseProbability

/-! # Field-dependent choices among finitely many lattice phases

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A union bound remains valid when the index is selected using the same
sample as the events. No measurability of the choice is needed. -/
theorem measure_selected_event_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Finset ι) (choice : Ω → ι) (E : ι → Set Ω)
    (hchoice : ∀ ω, choice ω ∈ F) {ε : ℝ≥0∞}
    (hE : ∀ i ∈ F, P (E i) ≤ ε) :
    P {ω | ω ∈ E (choice ω)} ≤ (F.card : ℝ≥0∞) * ε := by
  classical
  calc
    P {ω | ω ∈ E (choice ω)} ≤ P (⋃ i ∈ F, E i) := by
      apply measure_mono
      intro ω hω
      exact mem_iUnion.2 ⟨choice ω, mem_iUnion.2 ⟨hchoice ω, hω⟩⟩
    _ ≤ ∑ i ∈ F, P (E i) := measure_biUnion_finset_le F E
    _ ≤ ∑ _i ∈ F, ε := Finset.sum_le_sum hE
    _ = (F.card : ℝ≥0∞) * ε := by simp

/-- The third criterion holds with high probability for a field-dependent
choice from any prescribed finite set of phase sequences. The constants may
depend on an upper bound for the cardinality of that set. -/
theorem exists_universal_finite_phaseCriterion_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) (m : ℕ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (F : Finset (ℕ → ℂ)) (phase : Ω → ℕ → ℂ),
      F.card ≤ m → (∀ ω, phase ω ∈ F) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (phase ω)} ≤ δ := by
  have hpos : 0 < δ / ((m : ℝ≥0∞) + 1) := ENNReal.div_pos hδ.ne' (by simp)
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_singular_phaseCriterion_probability_all_radii
      (α := α) hgrowth hγ hγ₂ h₀ hμ₀ hb hpos
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd F phase hcard hchoice
  have h := measure_selected_event_le P F phase
    (fun q => {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) q}) hchoice
    (fun q _ => hbound N hN Ω P hC hcirc μ hgff hμ hE0 s hs x hd q)
  calc
    _ ≤ (F.card : ℝ≥0∞) * (δ / ((m : ℝ≥0∞) + 1)) := h
    _ ≤ ((m : ℝ≥0∞) + 1) * (δ / ((m : ℝ≥0∞) + 1)) := by
      gcongr
      exact le_trans (Nat.cast_le.mpr hcard) (le_add_right le_rfl)
    _ = δ := by rw [mul_comm, ENNReal.div_mul_cancel (by simp) (by simp)]

end HarmonicBalls.Section6
