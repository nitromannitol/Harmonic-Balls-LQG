import HarmonicBalls.Proofs.Sec8.SingularPhaseProbability
import HarmonicBalls.Proofs.Sec6.UniversalSizeWindows
import HarmonicBalls.Proofs.Sec6.SubrangePrevalenceMeasurable

/-! # Model-independent phase estimates

A single regular-field prevalence estimate fixes the phase criterion for
all whole-plane realizations. -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A fixed translation acts measurably on measures. -/
theorem measurable_measure_map_sub (q : ℂ) :
    Measurable (fun μ : Measure ℂ => μ.map (fun z : ℂ => z - q)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun μ : Measure ℂ => (μ.map (fun z : ℂ => z - q)) s)
  have hq : Measurable (fun z : ℂ => z - q) := measurable_id.sub measurable_const
  convert Measure.measurable_coe (hq hs) using 1
  funext μ
  exact Measure.map_apply hq hs

/-- For a fixed phase the third criterion is a measurable event in the measure. -/
theorem measurableSet_phaseCriterion_fixed (N : ℕ) (a b c : ℝ) (q : ℂ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    MeasurableSet {μ : Measure ℂ |
      PhaseVeryGoodCriterionThree μ 1 0 N a b c (fun _ => q)} := by
  have hm := (Section6.measurableSet_criterionThree_of_unit_good 1 (by norm_num)
    (-q) N a b c hunit).preimage (measurable_measure_map_sub q)
  convert hm using 1
  ext μ
  have h := phaseVeryGoodCriterionThree_map_add μ 1 0 (-q) N a b c (fun _ => q)
  simpa only [add_neg_cancel, zero_add, ← sub_eq_add_neg,
    phaseVeryGoodCriterionThree_zero, mem_ofPred_eq, mem_preimage, zero_sub] using h.symm

/-- A reference prevalence estimate fixes one index for every realization
and every common lattice phase. -/
theorem exists_universal_phaseCriterion_probability
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc ν → ∀ q : ℂ,
        P {ω | ¬ PhaseVeryGoodCriterionThree (ν ω) 1 0 N a b c (fun _ => q)} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_phaseVeryGoodCriterionThree_probability
    P₀ hγ hγ₂ hc h₀ hν₀ hAff₀ hCC₀ hprev hunit hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc ν h hν q => ?_⟩
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hν₀ hν
  have heq := hlaw.symm.measure_mem_eq (measurableSet_phaseCriterion_fixed N a b c q hunit).compl
  exact heq ▸ hbound N hN 0 (fun _ => q)

/-- One reference prevalence estimate gives singular-field phase bounds with
constants uniform over all target realizations. -/
theorem exists_universal_singular_phaseVeryGoodComparable_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ α β a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc →
        LQGMeasureCoordChange P γ 0 hC hcirc → LQGMeasureCoordChange P γ α hC hcirc →
      ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c q ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ δ + δ + δ + δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hw⟩ :=
    Section6.exists_universal_lqg_size_windows hgrowth hγ hγ₂ hα hβ P₀ h₀ hν₀ hδ
  obtain ⟨N₀, hN₀, hthree⟩ := exists_universal_phaseCriterion_probability
    P₀ hγ hγ₂ hc h₀ hν₀ hAff₀ hCC₀ hprev hunit hδ
  obtain ⟨m, hm, hcomp⟩ := exists_lqg_annulusBallComparison_uniform_threshold
    hfull γ α hγ hγ₂ hα hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hEx hW hAff hCC hCCα q
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have hd := origin_separated_from_scaled_annulus (ρ := 1) (by norm_num)
  have hcriterion := (measure_not_phaseVeryGoodCriterionThree_le_of_singular_weight P
    (x₀ := 0) (N₀ := N) (phase := fun _ => q) (by norm_num) hd
    (hN₀.trans hN) hweight).trans (hthree N hN Ω P hC hcirc ν hgff hν q)
  have hsize := hw Ω P hC hcirc μ hgff hμ hEx hW hAff hCC 1 (by norm_num) 0 hd
  have hgood : P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c q} ≤ δ + δ + δ := by
    calc
      _ ≤ _ := measure_not_phaseVeryGoodAnnulus_le P μ β 1 0 N _ b C₁m C₁p C₂m C₂p c q
      _ ≤ δ + δ + δ := add_le_add (add_le_add hsize.1 hsize.2) hcriterion
  calc
    _ ≤ P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c q} +
        P {ω | ¬ AnnulusBallComparison (μ ω) 0 0 m} := by
      convert measure_union_le (μ := P) _ _ using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, not_and_or]
    _ ≤ δ + δ + δ + δ := add_le_add hgood
      (hcomp Ω P hC hcirc μ hgff hμ hAff hCCα 0)

end HarmonicBalls
