import HarmonicBalls.Proofs.Sec6.RootedPhaseStability

/-! # Root-dependent centres in finite families

The phase-cover estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A root-dependent reference centre chosen from a finite deterministic set
and an arbitrary root-dependent phase satisfy the criterion-three estimate
up to the sum of the displacement-stability failure probabilities at the
candidate centres. Neither choice needs to be measurable. -/
theorem exists_rooted_finiteCentre_phaseCriterion_le_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (s : ℝ), 0 < s → ∀ (T : Finset ℂ) (a' b' : ℝ)
      (center : Ω × Z → ℂ) (phase : Ω × Z → ℕ → ℂ),
      (∀ p, center p ∈ T) →
      (P ⊗ₘ κ) {p | ¬ PhaseVeryGoodCriterionThree (μ p.1) s (center p) N a' b' (1 / 32) (phase p)} ≤
        (T.card : ℝ≥0∞) * δ +
          ∑ x ∈ T, P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} := by
  classical
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_rooted_phaseCriterion_probability_le_field_stability_failure hgrowth hγ hγ2 h hμ κ hκ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN s hs T a' b' center phase hcenter
  let E : ℂ → Set (Ω × Z) := fun x =>
    {p | ¬ PhaseVeryGoodCriterionThree (μ p.1) s x N a' b' (1 / 32) (phase p)}
  calc
    _ ≤ (P ⊗ₘ κ) (⋃ x ∈ T, E x) := by
      apply measure_mono
      intro p hp
      exact mem_iUnion.mpr ⟨center p, mem_iUnion.mpr ⟨hcenter p, hp⟩⟩
    _ ≤ ∑ x ∈ T, (P ⊗ₘ κ) (E x) := measure_biUnion_finset_le T E
    _ ≤ ∑ x ∈ T, (δ + P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'}) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hbound N hN s hs x a' b' phase
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The same estimate holds simultaneously for every candidate centre and
every phase, with no measurability requirement on a choice of witness. -/
theorem exists_rooted_finiteCentre_all_phases_le_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (s : ℝ), 0 < s → ∀ (T : Finset ℂ) (a' b' : ℝ),
      (P ⊗ₘ κ) {p | ∃ x ∈ T, ∃ phase : ℕ → ℂ,
        ¬ PhaseVeryGoodCriterionThree (μ p.1) s x N a' b' (1 / 32) phase} ≤
        (T.card : ℝ≥0∞) * δ +
          ∑ x ∈ T, P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} := by
  classical
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_rooted_finiteCentre_phaseCriterion_le_stability_failure hgrowth hγ hγ2 h hμ κ hκ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN s hs T a' b'
  by_cases hT : T.Nonempty
  · let I := {x : ℂ // x ∈ T} × (ℕ → ℂ)
    let : Nonempty I := ⟨⟨⟨hT.choose, hT.choose_spec⟩, fun _ => 0⟩⟩
    let E : I → Set (Ω × Z) := fun i =>
      {p | ¬ PhaseVeryGoodCriterionThree (μ p.1) s i.1.1 N a' b' (1 / 32) i.2}
    have hsel := measure_exists_event_le_of_selected (P ⊗ₘ κ) E
      (fun choice => hbound N hN s hs T a' b'
        (fun p => (choice p).1.1) (fun p => (choice p).2)
        (fun p => (choice p).1.2))
    have hsub : {p : Ω × Z | ∃ x ∈ T, ∃ phase : ℕ → ℂ,
        ¬ PhaseVeryGoodCriterionThree (μ p.1) s x N a' b' (1 / 32) phase} ⊆
        {p | ∃ i : I, p ∈ E i} := by
      intro p hp
      obtain ⟨x, hx, phase, hbad⟩ := hp
      exact ⟨⟨⟨x, hx⟩, phase⟩, hbad⟩
    exact (measure_mono hsub).trans hsel
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [he]

end HarmonicBalls.Section6
