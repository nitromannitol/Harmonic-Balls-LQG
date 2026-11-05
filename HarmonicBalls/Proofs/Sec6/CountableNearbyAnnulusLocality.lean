import HarmonicBalls.Proofs.Sec6.ThickAnnulusIteration
import HarmonicBalls.Proofs.Sec6.CompactUniformCountableProbability
import HarmonicBalls.Proofs.Sec6.RecenteredLocalityTranslation
import HarmonicBalls.Proofs.Sec8.AEGermTriviality
import HarmonicBalls.Proofs.Sec6.GoodAnnulusDyadicLaw

/-! # Countable nearby-centre good-annulus events

The underlying fine-support and iteration arguments use Leonardo Bonanno's
proof in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- Countably many nearby good-annulus events are local in one thick annulus.
The centres are deterministic; no continuity in the centre is assumed. -/
theorem isFieldMeasurableModConst_countable_nearby_goodAnnuli
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (b : ℝ) (z : ℕ → ℂ)
    (hz : ∀ i, z i ∈ ball 0 (r / 100)) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (2 * r) (6 * r))
      {ω | ∀ i, IsGoodAnnulus (μ ω) r (z i) a b} := by
  classical
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hlocal (i : ℕ) : IsFieldMeasurableModConst P 0 hC
      (annulus (z i) (3 * r) (5 * r))
      {ω | IsGoodAnnulus (μ ω) r (z i) a b} := by
    have hreg := ae_lqg_goodAnnulus_regular (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth)
      hγ hγ2 hQ h hμ (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc) hr (z i) ha
    have hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0 := hreg.mono fun _ hω => hω.1
    have hfin : ∀ᵐ ω ∂P, μ ω (annulus (z i) (3 * r) (5 * r)) ≠ ∞ :=
      hreg.mono fun _ hω => hω.2.1
    have hpos : ∀ᵐ ω ∂P, 0 < μ ω (annulus (z i) (3 * r) (5 * r)) := by
      filter_upwards [hreg] with ω hω
      exact bot_lt_iff_ne_bot.mpr ((mul_ne_zero_iff.mp hω.2.2.ne').2)
    exact isFieldMeasurableModConst_goodAnnulus_of_null_frontier h hμ hr (z i) ha b
      hatom hfin hpos
      (by intro v hv x hx hne; exact planarBrownianMotion_point_avoidance v x hne.symm)
      (ae_lqg_annulus_frontier_eq_zero_of_translation h hμ hAff (z i) (3 * r) (5 * r))
  choose E hE hEq using hlocal
  refine ⟨⋂ i, E i, ?_, ?_⟩
  · apply MeasurableSet.iInter
    intro i
    exact (fieldSigmaAlgebraModConst_mono 0 hC
      (nearby_goodAnnulus_subset_thick_annulus hr (hz i))) _ (hE i)
  · filter_upwards [ae_all_iff.mpr hEq] with ω hω
    simp only [mem_iInter]
    exact propext (forall_congr' (fun i => iff_of_eq (hω i)))

/-- At radius one, a single threshold gives high probability simultaneously
for every prescribed countable family of nearby centres. -/
theorem exists_countable_nearby_unit_goodAnnuli_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ z : ℕ → ℂ,
      (∀ i, z i ∈ ball 0 ((1 : ℝ) / 100)) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) 1 (z i) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ := exists_compact_uniform_countable_goodAnnulus_probability
    hgrowth hγ hγ2 h hμ (isCompact_closedBall (0 : ℂ) ((1 : ℝ) / 100))
    (isCompact_singleton : IsCompact ({(1 : ℝ)} : Set ℝ))
    (by simp : ({(1 : ℝ)} : Set ℝ) ⊆ Ioi 0) hb hδ
  refine ⟨a, ha, ?_⟩
  intro z hz
  exact hbound z (fun _ => 1) (fun i => ball_subset_closedBall (hz i)) (by simp)

/-- One threshold controls countable neighborhoods at all dyadic scales and
all phases in `[1/2, 1]`. -/
theorem exists_countable_nearby_dyadic_goodAnnuli_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ n : ℕ, ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      ∀ z : ℕ → ℂ, (∀ i, z i ∈ ball 0 (s / 100)) →
      P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (s * dyadicScale n)
        (dyadicScale n • z i) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ := exists_compact_uniform_countable_goodAnnulus_probability
    hgrowth hγ hγ2 h hμ (isCompact_closedBall (0 : ℂ) ((1 : ℝ) / 100))
    (isCompact_Icc : IsCompact (Icc (1 / 2 : ℝ) 1)) (by intro t ht; change 0 < t; linarith [ht.1]) hb hδ
  refine ⟨a, ha, ?_⟩
  intro n s hs z hz
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  have hkr : k * dyadicScale n = 1 := by
    dsimp [k]
    simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
  have hr : 0 < s * dyadicScale n := mul_pos (by linarith [hs.1]) (dyadicScale_pos n)
  have hmeas : MeasurableSet {m : Measure ℂ | ∃ i,
      ¬ IsGoodAnnulus m (s * dyadicScale n) (dyadicScale n • z i) a b} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun i =>
      (measurableSet_isGoodAnnulus_of_pos _ hr _ a b ha.1).compl
  have hd := (identDistrib_normalizedPullback_dyadic hγ h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) n).measure_mem_eq hmeas
  change P {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) (s * dyadicScale n)
      (dyadicScale n • z i) a b} =
    P {ω | ∃ i, ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
      (s * dyadicScale n) (dyadicScale n • z i) a b} at hd
  have heq : {ω | ∃ i, ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω))
      (s * dyadicScale n) (dyadicScale n • z i) a b} =
      {ω | ∃ i, ¬ IsGoodAnnulus (μ ω) s (z i) a b} := by
    ext ω
    simp only [mem_ofPred_eq, normalizedPullbackMeasure]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (γ * (lqgQ γ * Real.log k + fieldCircleAverage 0 (hcirc ω) k 0)))⁻¹
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
    apply exists_congr
    intro i
    change ¬ IsGoodAnnulus (c • (μ ω).map (fun x : ℂ => k⁻¹ • x))
      (s * dyadicScale n) (dyadicScale n • z i) a b ↔ _
    rw [isGoodAnnulus_smul _ _ _ _ _ hc0 hct, isGoodAnnulus_map_inv_smul_iff hk]
    have hscale : k * (s * dyadicScale n) = s := by
      calc
        _ = s * (k * dyadicScale n) := by ring
        _ = s := by rw [hkr, mul_one]
    have hcenter : k • (dyadicScale n • z i) = z i := by rw [smul_smul, hkr, one_smul]
    rw [hscale, hcenter]
  rw [heq] at hd
  rw [hd]
  apply hbound z (fun _ => s)
  · intro i
    apply ball_subset_closedBall
    exact (ball_subset_ball (by linarith [hs.2])) (hz i)
  · intro i
    exact hs

end HarmonicBalls.Section6
