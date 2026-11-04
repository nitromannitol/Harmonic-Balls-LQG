import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodScaling
import HarmonicBalls.Proofs.Sec8.UniformAnnulusThreshold

/-! # Probability bounds for shifted very-good annuli

The two size windows and the phase-uniform lattice estimate give a uniform
one-scale bound for the complete shifted event. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A union bound for the three criteria of the shifted event. -/
theorem measure_not_phaseVeryGoodAnnulus_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (β ρ : ℝ) (x : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) :
    P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃ phase} ≤
      P {ω | annulusBallMassSize (μ ω) β ρ x / (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} +
      P {ω | annulusGreenPotentialSup (μ ω) x (ρ / 4) (2 * ρ) /
        (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} +
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b C₃ (fun _ => phase)} := by
  let A : Set Ω := {ω | annulusBallMassSize (μ ω) β ρ x /
    (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉ Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)}
  let B : Set Ω := {ω | annulusGreenPotentialSup (μ ω) x (ρ / 4) (2 * ρ) /
    (μ ω) (annulus x (ρ / 4) (2 * ρ)) ∉ Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)}
  let C : Set Ω := {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b C₃ (fun _ => phase)}
  have hsub : {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃ phase} ⊆
      (A ∪ B) ∪ C := by
    intro ω hω
    by_contra h
    have ha : ω ∉ A := fun ha => h (Or.inl (Or.inl ha))
    have hb : ω ∉ B := fun hb => h (Or.inl (Or.inr hb))
    have hc : ω ∉ C := fun hc => h (Or.inr hc)
    exact hω ⟨not_not.mp ha, not_not.mp hb, not_not.mp hc⟩
  calc
    _ ≤ P ((A ∪ B) ∪ C) := measure_mono hsub
    _ ≤ P (A ∪ B) + P C := measure_union_le _ _
    _ ≤ P A + P B + P C := by gcongr; exact measure_union_le _ _

/-- A fixed-phase bound for the full event also holds for any independent
random phase. -/
theorem measure_prod_not_phaseVeryGoodAnnulus_le
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [SFinite P] (Q : Measure T) [IsProbabilityMeasure Q]
    {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfinite : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {phase : T → ℂ} (hphase : Measurable phase)
    (β ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hbound : ∀ q : ℂ,
      P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃ q} ≤ δ) :
    (Q.prod P) {p : T × Ω |
      ¬ PhaseVeryGoodAnnulus (μ p.2) β ρ x N a b C₁m C₁p C₂m C₂p C₃ (phase p.1)} ≤ δ := by
  have hs : MeasurableSet {p : T × Ω |
      ¬ PhaseVeryGoodAnnulus (μ p.2) β ρ x N a b C₁m C₁p C₂m C₂p C₃ (phase p.1)} :=
    (measurableSet_phaseVeryGoodAnnulus (hμ.comp measurable_snd)
      (fun p => hfinite p.2) measurable_const (hphase.comp measurable_fst)
      β ρ hρ N a b C₁m C₁p C₂m C₂p C₃ hunit).compl
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ : T, δ ∂Q := lintegral_mono (fun t => hbound (phase t))
    _ = δ := by simp

/-- Uniform joint bounds pass to an independent random phase. -/
theorem measure_prod_not_phaseVeryGoodComparable_le
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [SFinite P] (Q : Measure T) [IsProbabilityMeasure Q]
    {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfinite : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {phase : T → ℂ} (hphase : Measurable phase)
    (β ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (N n : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hbound : ∀ q : ℂ,
      P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β ρ x N a b C₁m C₁p C₂m C₂p C₃ q ∧
        AnnulusBallComparison (μ ω) n x m)} ≤ δ) :
    (Q.prod P) {p : T × Ω |
      ¬ (PhaseVeryGoodAnnulus (μ p.2) β ρ x N a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (μ p.2) n x m)} ≤ δ := by
  have hs : MeasurableSet {p : T × Ω |
      ¬ (PhaseVeryGoodAnnulus (μ p.2) β ρ x N a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (μ p.2) n x m)} := by
    apply MeasurableSet.compl
    exact (measurableSet_phaseVeryGoodAnnulus (hμ.comp measurable_snd)
      (fun p => hfinite p.2) measurable_const (hphase.comp measurable_fst)
      β ρ hρ N a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (hμ.comp measurable_snd)
        (fun p => hfinite p.2) measurable_const n m)
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ : T, δ ∂Q := lintegral_mono (fun t => hbound (phase t))
    _ = δ := by simp

universe u

/-- Uniform one-scale control of the full shifted event, using the stated
volume growth, prevalence, affine and coordinate-change hypotheses. -/
theorem exists_phaseVeryGoodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (x phase : ℂ),
      P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 x N a b C₁m C₁p C₂m C₂p c phase} ≤
        δ + δ + δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hw⟩ :=
    Section6.exists_wholePlane_veryGood_size_windows_uniform hgrowth P hγ hγ₂ hβ
      hgff hμ hAff hCC hδ
  obtain ⟨N₀, hN₀, hthree⟩ :=
    exists_phaseVeryGoodCriterionThree_probability P hγ hγ₂ hc hgff hμ hAff hCC hprev hunit hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN x phase
  calc
    _ ≤ _ := measure_not_phaseVeryGoodAnnulus_le P μ β 1 x N a b C₁m C₁p C₂m C₂p c phase
    _ ≤ δ + δ + δ := add_le_add (add_le_add (hw 1 (by norm_num) x).1
      (hw 1 (by norm_num) x).2) (hthree N hN x (fun _ => phase))

/-- At the unit scale, the full shifted event and annulus-ball comparison
have a uniform joint bound for every deterministic phase. -/
theorem exists_phaseVeryGoodComparable_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ β : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ phase : ℂ,
      P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N a b C₁m C₁p C₂m C₂p c phase ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ δ + δ + δ + δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, hgood⟩ :=
    exists_phaseVeryGoodAnnulus_probability hgrowth P hγ hγ₂ hβ hc hgff hμ hAff hCC hprev hunit hδ
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨m, hm, hcomp⟩ := exists_lqg_annulusBallComparison_uniform_threshold
    hfull γ 0 hγ hγ₂ hQ hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN phase
  calc
    _ ≤ P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N a b C₁m C₁p C₂m C₂p c phase} +
        P {ω | ¬ AnnulusBallComparison (μ ω) 0 0 m} := by
      convert measure_union_le (μ := P)
        {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N a b C₁m C₁p C₂m C₂p c phase}
        {ω | ¬ AnnulusBallComparison (μ ω) 0 0 m} using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, not_and_or]
    _ ≤ δ + δ + δ + δ := add_le_add (hgood N hN 0 phase)
      (hcomp Ω P hC hcirc μ hgff hμ hAff hCC 0)

end HarmonicBalls
