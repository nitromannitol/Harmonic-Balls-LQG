import HarmonicBalls.Proofs.Sec6.CountableNearbyAnnulusLocality

/-! # Countable nearby-centre annulus iteration

The iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Positive dilation preserves the normalized relative-centre condition. -/
theorem smul_mem_nearby_ball {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ ball 0 ((1 : ℝ) / 100)) : s • z ∈ ball 0 (s / 100) := by
  have h := mem_ball.mp hz
  change dist (s • z) 0 < s / 100
  rw [← smul_zero s, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs]
  nlinarith

/-- Dyadic scaling preserves the failure probability for a countable family
of centres specified relative to the radius. -/
theorem countable_nearby_bad_probability_eq_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (b : ℝ) (n : ℕ) (z : ℕ → ℂ) :
    P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n)
      ((r * dyadicScale n) • z i) a b} =
    P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) r (r • z i) a b} := by
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  have hkr : k * dyadicScale n = 1 := by
    dsimp [k]
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have hr' : 0 < r * dyadicScale n := mul_pos hr (dyadicScale_pos n)
  have hm : MeasurableSet {m : Measure ℂ | ∃ i,
      ¬ IsGoodAnnulus m (r * dyadicScale n) ((r * dyadicScale n) • z i) a b} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun i =>
      (measurableSet_isGoodAnnulus_of_pos _ hr' _ a b ha).compl
  have hd := (identDistrib_normalizedPullback_dyadic hγ h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) n).measure_mem_eq hm
  change P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n)
      ((r * dyadicScale n) • z i) a b} =
    P {ω | ∃ i, ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
      (r * dyadicScale n) ((r * dyadicScale n) • z i) a b} at hd
  have heq : {ω | ∃ i, ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
      (r * dyadicScale n) ((r * dyadicScale n) • z i) a b} =
      {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) r (r • z i) a b} := by
    ext ω
    simp only [mem_ofPred_eq, normalizedPullbackMeasure]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (γ * (lqgQ γ * Real.log k + fieldCircleAverage 0 (hcirc ω) k 0)))⁻¹
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
    apply exists_congr
    intro i
    change ¬ IsGoodAnnulus (c • (μ ω).map (fun x : ℂ => k⁻¹ • x))
      (r * dyadicScale n) ((r * dyadicScale n) • z i) a b ↔ _
    rw [isGoodAnnulus_smul _ _ _ _ _ hc0 hct, isGoodAnnulus_map_inv_smul_iff hk]
    have hscale : k * (r * dyadicScale n) = r := by
      calc
        _ = r * (k * dyadicScale n) := by ring
        _ = r := by rw [hkr, mul_one]
    rw [smul_smul, hscale]
  rw [heq] at hd
  exact hd

/-- A fixed threshold controls every countable family of relative nearby
centres, at every positive radius. -/
theorem exists_countable_nearby_goodAnnuli_probability_all_radii
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r → ∀ z : ℕ → ℂ,
      (∀ i, z i ∈ ball 0 ((1 : ℝ) / 100)) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) r (r • z i) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ :=
    exists_countable_nearby_dyadic_goodAnnuli_probability hgrowth hγ hγ2 h hμ hb hδ
  refine ⟨a, ha, ?_⟩
  have hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ z : ℕ → ℂ,
      (∀ i, z i ∈ ball 0 ((1 : ℝ) / 100)) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) r (r • z i) a b} ≤ δ := by
    intro r hr hr1 z hz
    obtain ⟨s, n, hs, rfl⟩ := exists_dyadic_phase hr hr1
    have hbnd := hbound n s ⟨hs.1.le, hs.2⟩ (fun i => s • z i)
      (fun i => smul_mem_nearby_ball (by linarith [hs.1]) (hz i))
    simpa only [smul_smul, mul_comm] using hbnd
  intro r hr z hz
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hnpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.le_of_lt n.lt_two_pow_self
  have hn' : r ≤ (2 : ℝ) ^ n := hn.le.trans hnpow
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have heq : r * dyadicScale n = r / (2 : ℝ) ^ n := by
    simp [dyadicScale, inv_pow, div_eq_mul_inv]
  have hpos : 0 < r * dyadicScale n := mul_pos hr (dyadicScale_pos n)
  have hle : r * dyadicScale n ≤ 1 := by rw [heq]; exact (div_le_one hpow).2 hn'
  rw [← countable_nearby_bad_probability_eq_dyadic hγ h hμ hr ha.1 b n z]
  exact hsmall _ hpos hle z hz

/-- A countable family of relative nearby centres has a polynomial lower-tail
bound for the number of radii at which all centres are good. The family is
deterministic and the constants do not depend on the radius or family. -/
theorem exists_countable_nearby_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ z : ℕ → ℂ, (∀ i, z i ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (μ ω) (s * r) ((s * r) • z i) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  obtain ⟨p, hp, C, hCpos, hiter⟩ := thick_annulus_subrange_probability α β hα hβ
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.mpr (by linarith [hp.2])
  obtain ⟨a, ha, hprob⟩ :=
    exists_countable_nearby_goodAnnuli_probability_all_radii hgrowth hγ hγ2 h hμ hb hδ
  refine ⟨a, ha, C, hCpos, ?_⟩
  intro z hz s hs ε hε ht
  let := h.isProbabilityMeasure
  apply hiter Ω P hC hcirc h s hs (fun ω r => ∀ i, IsGoodAnnulus (μ ω) r (r • z i) a b)
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := mul_pos hs (pow_pos (by norm_num) n)
    exact isFieldMeasurableModConst_countable_nearby_goodAnnuli hgrowth hγ hγ2 h hμ hr ha.1 b
      (fun i => (s * (7 : ℝ)⁻¹ ^ n) • z i) (fun i => smul_mem_nearby_ball hr (hz i))
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := mul_pos hs (pow_pos (by norm_num) n)
    apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
    simpa only [Set.compl_ofPred, not_forall] using hprob _ hr z hz
  · exact hε
  · exact ht

/-- A translated normalized measure preserves good annuli at arbitrary
translated centres. -/
theorem isGoodAnnulus_affineMeasure_translate_at
    {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (r : ℝ) (x z : ℂ) (a b : ℝ) (ω : Ω) :
    IsGoodAnnulus (affineMeasure γ hcirc μ 1 x ω) r z a b ↔
      IsGoodAnnulus (μ ω) r (x + z) a b := by
  unfold affineMeasure
  rw [isGoodAnnulus_smul _ _ _ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    ENNReal.ofReal_ne_top]
  have hx : x + z + -x = z := by abel
  simpa only [div_one, sub_eq_add_neg, hx] using
    isGoodAnnulus_map_add_iff (-x) (μ ω) r (x + z) a b

/-- The polynomial count bound is uniform in the reference centre. -/
theorem exists_countable_nearby_goodAnnuli_count_tail_all_centres
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℂ) (z : ℕ → ℂ), (∀ i, z i ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (μ ω) (s * r) (x + (s * r) • z i) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  obtain ⟨p, hp, C, hCpos, hiter⟩ := thick_annulus_subrange_probability α β hα hβ
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.mpr (by linarith [hp.2])
  obtain ⟨a, ha, hprob⟩ :=
    exists_countable_nearby_goodAnnuli_probability_all_radii hgrowth hγ hγ2 h hμ hb hδ
  refine ⟨a, ha, C, hCpos, ?_⟩
  intro x z hz s hs ε hε ht
  let := h.isProbabilityMeasure
  let ν := affineMeasure γ hcirc μ 1 x
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hrec : IsWholePlaneGFF P (affinePairing hC hcirc 1 x) (affineCircle hcirc 1 x) :=
    hAff h 1 one_ne_zero x
  have hν : IsLQGMeasureOfField P γ 0 (affineCircle hcirc 1 x) ν :=
    isLQGMeasureOfField_translate h hμ x
  have hprobν (r : ℝ) (hr : 0 < r) :
      P {ω | ∃ i, ¬ IsGoodAnnulus (ν ω) r (r • z i) a b} ≤ ENNReal.ofReal (1 - p) := by
    have hm : MeasurableSet {m : Measure ℂ | ∃ i, ¬ IsGoodAnnulus m r (r • z i) a b} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i => (measurableSet_isGoodAnnulus_of_pos r hr _ a b ha.1).compl
    have heq := (identDistrib_translateMeasure h hμ hAff x).measure_mem_eq hm
    change P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) r (r • z i) a b} =
      P {ω | ∃ i, ¬ IsGoodAnnulus (ν ω) r (r • z i) a b} at heq
    rw [← heq]
    exact hprob r hr z hz
  have htail := hiter Ω P (affinePairing hC hcirc 1 x) (affineCircle hcirc 1 x) hrec s hs
    (fun ω r => ∀ i, IsGoodAnnulus (ν ω) r (r • z i) a b)
    (by
      intro n
      have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := mul_pos hs (pow_pos (by norm_num) n)
      exact isFieldMeasurableModConst_countable_nearby_goodAnnuli hgrowth hγ hγ2 hrec hν hr ha.1 b
        (fun i => (s * (7 : ℝ)⁻¹ ^ n) • z i) (fun i => smul_mem_nearby_ball hr (hz i)))
    (by
      intro n
      have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := mul_pos hs (pow_pos (by norm_num) n)
      apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
      simpa only [Set.compl_ofPred, not_forall] using hprobν _ hr)
    ε hε ht
  simpa only [ν, isGoodAnnulus_affineMeasure_translate_at] using htail

end HarmonicBalls.Section6
