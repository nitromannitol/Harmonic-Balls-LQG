import HarmonicBalls.Proofs.Sec6.RootedNearbyAnnulusCounts
import HarmonicBalls.Proofs.Sec6.UniformFixedCentreCover

/-! # Rooted phase estimates conditional on displacement stability

The finite phase-cover estimates use Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Under normalized root sampling, arbitrary root-dependent phases satisfy
criterion three up to the probability of failure of the good-annulus
small-displacement transfer. The reference centre remains deterministic. -/
theorem exists_rooted_phaseCriterion_probability_le_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (a' b' : ℝ) (phase : Ω × Z → ℕ → ℂ),
      (P ⊗ₘ κ) {p | ¬ PhaseVeryGoodCriterionThree (μ p.1) s x N a' b' (1 / 32) (phase p)} ≤
        δ + (P ⊗ₘ κ) {p | ¬ HasNearbyGoodAnnulusTransfer (μ p.1) s x N a b a' b'} := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_nearbyCentre_phaseCounts_probability hgrowth hγ hγ2 h hμ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN s hs x a' b' phase
  obtain ⟨F, hcard, hcover⟩ := exists_dyadic_phase_displacement hs
  have hF : ∀ n, (F n).Nonempty := by
    intro n
    obtain ⟨q, hq, _⟩ := hcover n 0
    exact ⟨q, hq⟩
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  have hpre := Measure.le_map_apply (μ := P ⊗ₘ κ) measurable_fst.aemeasurable
    {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N a b (1 / 32) F}
  rw [hp.map_eq] at hpre
  simp only [preimage_ofPred_eq] at hpre
  have hnear : (P ⊗ₘ κ) {p | ¬ HasNearbyCentrePhaseCounts (μ p.1) s x N a b (1 / 32) F} ≤ δ :=
    hpre.trans (hbound N hN Ω P hC hcirc μ h hμ s hs x F hcard hF)
  calc
    _ ≤ (P ⊗ₘ κ) {p | ¬ HasNearbyCentrePhaseCounts (μ p.1) s x N a b (1 / 32) F} +
        (P ⊗ₘ κ) {p | ¬ HasNearbyGoodAnnulusTransfer (μ p.1) s x N a b a' b'} :=
      measure_bad_phaseCriterion_le_nearby_failures (P ⊗ₘ κ) (fun p => μ p.1)
        hs x N a b a' b' (1 / 32) F hcover phase
    _ ≤ _ := add_le_add hnear le_rfl

/-- The stability error may be estimated under the original field law,
without assuming measurability of the stability failure event. -/
theorem exists_rooted_phaseCriterion_probability_le_field_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (a' b' : ℝ) (phase : Ω × Z → ℕ → ℂ),
      (P ⊗ₘ κ) {p | ¬ PhaseVeryGoodCriterionThree (μ p.1) s x N a' b' (1 / 32) (phase p)} ≤
        δ + P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_rooted_phaseCriterion_probability_le_stability_failure hgrowth hγ hγ2 h hμ κ hκ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN s hs x a' b' phase
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  have hpre := Measure.le_map_apply (μ := P ⊗ₘ κ) measurable_fst.aemeasurable
    {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'}
  rw [hp.map_eq] at hpre
  simp only [preimage_ofPred_eq] at hpre
  exact (hbound N hN s hs x a' b' phase).trans (add_le_add le_rfl hpre)

end HarmonicBalls.Section6
