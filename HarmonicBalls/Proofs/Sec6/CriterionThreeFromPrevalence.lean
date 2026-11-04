import HarmonicBalls.Proofs.Sec6.CriterionThreeLocalComparison
import HarmonicBalls.Proofs.Sec6.Prevalence

/-! # The third criterion from prevalence of good annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- On the unit annulus, a sufficiently fine lattice is contained in the
prevalence grid. -/
theorem unit_annulus_lattice_subset_prevalenceGrid {n : ℕ} (hn : 9 ≤ n) :
    scaledLattice (dyadicScale n / 100) ∩ annulus (0 : ℂ) (1 / 2) 1 ⊆
      prevalenceGrid (dyadicScale n) := by
  intro z hz
  have hsq := sqrt_dyadicScale_le_one_twentieth hn
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hzouter : dist z (0 : ℂ) < 1 := hz.2.1
  have hzinner : 1 / 2 < dist z (0 : ℂ) := lt_of_not_ge hz.2.2
  refine ⟨⟨?_, ?_⟩, hz.1⟩
  · change dist z 0 < 1 + dyadicScale n
    linarith
  · change ¬ dist z 0 < 10 * Real.sqrt (dyadicScale n)
    linarith

/-- A single fine-scale subrange prevalence event implies the corresponding
count in criterion three at unit scale. -/
theorem criterionThree_count_of_subrange_prevalence
    {μ : Measure ℂ} {c a b : ℝ} (hc : 0 < c) {n : ℕ} (hn : 9 ≤ n)
    (h : ∀ z ∈ prevalenceGrid (dyadicScale n),
      c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)) :
    ∀ z ∈ scaledLattice (dyadicScale n * 1 / 100) ∩ annulus (0 : ℂ) (1 / 2) 1,
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  intro z hz
  have hε0 : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  have hε1 : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hz' : z ∈ prevalenceGrid (dyadicScale n) :=
    unit_annulus_lattice_subset_prevalenceGrid hn (by simpa using hz)
  refine ((logb_neg_half_le (by norm_num) hc hε0 hε1).trans (h z hz')).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ?_) ?_
  · have hr_sqrt : r ≤ Real.sqrt (dyadicScale n) := by
      refine hr.1.2.trans ?_
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    obtain ⟨k, hk⟩ := hr.2.1
    have hk1 : 1 ≤ k := by
      by_contra hk1
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      linarith
    exact ⟨by simpa using ⟨hr.1.1, hr_sqrt⟩, ⟨k, hk1, by simpa using hk⟩, hr.2.2⟩
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
      (by norm_num) (by norm_num) hε0 fun r hr => ⟨by simpa using hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

/-- Almost-sure eventual prevalence gives criterion three for some sufficiently
large starting index. -/
theorem ae_exists_criterionThree_of_subrange_prevalence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ : Ω → Measure ℂ}
    {c a b : ℝ} (hc : 0 < c)
    (h : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}) :
    ∀ᵐ ω ∂P, ∃ N₀ : ℕ, VeryGoodCriterionThree (μ ω) 1 0 N₀ a b c := by
  filter_upwards [h.ae_eventually_dyadic] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨max N 9, fun n hn => ?_⟩
  exact criterionThree_count_of_subrange_prevalence hc ((le_max_right N 9).trans hn)
    (hN n ((le_max_left N 9).trans hn))


/-- Subrange prevalence gives criterion three with arbitrarily high probability
at unit scale, without assuming measurability of the individual events. -/
theorem exists_criterionThree_probability_of_subrange_prevalence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ : Ω → Measure ℂ}
    {c a b : ℝ} (hc : 0 < c)
    (h : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} ≤ δ := by
  by_cases hδtop : δ = ∞
  · exact ⟨9, le_rfl, fun N hN => by rw [hδtop]; exact le_top⟩
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  obtain ⟨p, hp, C, r₀, hr₀, htail⟩ := h.dyadic_tail (a := 1) (c := 1) one_pos one_pos
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
  refine ⟨max M 9, le_max_right M 9, fun N hN => ?_⟩
  calc P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} ≤
      P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ 1 * r ^ (1 : ℝ) →
        ω ∈ {ω | ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ j),
          c * Real.logb 7 (((2 : ℝ)⁻¹ ^ j) ^ (-1 : ℝ)) ≤
            ({s : ℝ | s ∈ Icc ((2 : ℝ)⁻¹ ^ j) (((2 : ℝ)⁻¹ ^ j) ^ (3 / 4 : ℝ)) ∧
              (∃ k : ℕ, s = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) s z a b}.ncard : ℝ)}}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        have hnM : M ≤ n := (le_max_left M 9).trans (hN.trans hn)
        have hn9 : 9 ≤ n := (le_max_right M 9).trans (hN.trans hn)
        have hpow : (2 : ℝ)⁻¹ ^ n ≤ r :=
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnM).trans hM.le
        apply criterionThree_count_of_subrange_prevalence hc hn9
        apply hgood n
        simpa only [Real.rpow_one, one_mul] using hpow
    _ ≤ ENNReal.ofReal (C * r ^ p) := htail r hr hrr₀
    _ ≤ δ := hsmall

end HarmonicBalls.Section6
