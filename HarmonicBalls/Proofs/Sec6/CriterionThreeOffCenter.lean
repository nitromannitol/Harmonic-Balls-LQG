import HarmonicBalls.Proofs.Sec6.SubrangePrevalenceMeasurable
import HarmonicBalls.Proofs.Sec6.CriterionThreeLatticeApprox
import HarmonicBalls.Proofs.Sec6.DyadicFailureTail

/-! # Uniform off-center criterion-three probability -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Polynomial bounds on individual dyadic failures give one starting index
that works uniformly for every dominated family of events. -/
theorem exists_uniform_dyadic_failure_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : ℝ → Set Ω}
    (h : PolyHighProb P E) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ F : ℕ → Set Ω,
      (∀ n, P (F n)ᶜ ≤ P (E ((2 : ℝ)⁻¹ ^ n))ᶜ) →
      P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ ≤ δ := by
  by_cases hδtop : δ = ∞
  · exact ⟨9, le_rfl, fun N hN F hF => by rw [hδtop]; exact le_top⟩
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  obtain ⟨p, hp, C, r₀, hr₀, htail⟩ :=
    dyadic_tail_of_failure_probability_bounds P h (a := 1) (c := 1) one_pos one_pos
  obtain ⟨r₁, hr₁, hrpow⟩ := exists_pos_forall_rpow_le hp
    (div_pos hδreal (by positivity : 0 < max C 0 + 1))
  let r : ℝ := min r₀ r₁ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : r < r₀ := by dsimp [r]; linarith [min_le_left r₀ r₁, lt_min hr₀ hr₁]
  have hrr₁ : r < r₁ := by dsimp [r]; linarith [min_le_right r₀ r₁, lt_min hr₀ hr₁]
  have hreal : C * r ^ p ≤ δ.toReal := by
    have hrp := hrpow r hr hrr₁
    have hrp0 : 0 ≤ r ^ p := Real.rpow_nonneg hr.le _
    have hC : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
    have hmul := mul_le_mul_of_nonneg_right hC hrp0
    have hm := mul_le_mul_of_nonneg_left hrp (by positivity : 0 ≤ max C 0 + 1)
    have heq : (max C 0 + 1) * (δ.toReal / (max C 0 + 1)) = δ.toReal := by
      field_simp
    linarith
  have hsmall : ENNReal.ofReal (C * r ^ p) ≤ δ := by
    calc ENNReal.ofReal (C * r ^ p) ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal hreal
      _ = δ := ENNReal.ofReal_toReal hδtop
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨max M 9, le_max_right M 9, fun N hN F hF => ?_⟩
  calc P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ ≤
      P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ 1 * r ^ (1 : ℝ) → ω ∈ F j}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        have hnM : M ≤ n := (le_max_left M 9).trans (hN.trans hn)
        have hpow : (2 : ℝ)⁻¹ ^ n ≤ r :=
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnM).trans hM.le
        apply hgood n
        simpa only [Real.rpow_one, one_mul] using hpow
    _ ≤ ENNReal.ofReal (C * r ^ p) := htail F hF r hr hrr₀
    _ ≤ δ := hsmall

/-- A whole-plane subrange prevalence estimate gives one starting index for
criterion three at every center of a unit annulus. -/
theorem exists_offCenter_unit_criterionThree_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ x : ℂ,
      P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 x N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_uniform_dyadic_failure_tail_bound P hprev hδ
  refine ⟨N₀, hN₀, fun N hN x => ?_⟩
  have hpos (n : ℕ) : 0 < dyadicScale n / 100 := by
    unfold dyadicScale
    positivity
  choose y hy hxy using fun n : ℕ => exists_scaledLattice_dist_lt x (hpos n)
  let F : ℕ → Set Ω := fun n => {ω | ∀ z ∈ prevalenceGrid (dyadicScale n),
    c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus ((μ ω).map (fun w : ℂ => w + -(y n))) r z a b}.ncard : ℝ)}
  have hF : ∀ n, P (F n)ᶜ ≤ P {ω | ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ n),
      c * Real.logb 7 (((2 : ℝ)⁻¹ ^ n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ((2 : ℝ)⁻¹ ^ n) (((2 : ℝ)⁻¹ ^ n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}ᶜ := by
    intro n
    have heq := measure_subrange_prevalence_failure_translate hγ hγ₂ hgff hμ hAff hCC
      (dyadicScale n) a b c (y n) hunit
    simpa only [F, dyadicScale, compl_ofPred] using heq.symm.le
  calc P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 x N a b c} ≤
      P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        apply criterionThree_count_of_translated_subrange_prevalence hc
          (hN₀.trans (hN.trans hn)) (hy n) (hxy n)
        exact hgood n hn
    _ ≤ δ := hbound N hN F hF

universe u

/-- A reference prevalence estimate supplies one index for all centers and
all realizations of the whole-plane LQG measure. -/
theorem exists_universal_offCenter_unit_criterionThree_probability
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    {μ₀ : Ω₀ → Measure ℂ} {a b c : ℝ} (hc : 0 < c)
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ x : ℂ, P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 x N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_offCenter_unit_criterionThree_probability
    P₀ hγ hγ₂ hc h₀ hμ₀ hAff₀ hCC₀ hprev hunit hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc μ h hμ x => ?_⟩
  have hlaw := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hmeas := (measurableSet_criterionThree_of_unit_good 1 (by norm_num) x N a b c hunit).compl
  have heq := hlaw.symm.measure_mem_eq hmeas
  exact heq ▸ hbound N hN x

end HarmonicBalls.Section6
