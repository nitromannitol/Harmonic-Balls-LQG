import HarmonicBalls.Proofs.Sec6.SingularRootSeparatedTail

/-! # Good annuli at singular roots near the origin

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology
universe u

/-- A singular LQG root sampled from the unit disk avoids the origin. -/
theorem ae_singular_unitDisc_root_ne_zero
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const), p.2 ≠ 0 := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hm := h.aemeasurable_lqgMeasure hμ
  let κ := weightedRestrictionKernel P μ hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  apply Measure.ae_compProd_of_ae_ae ((measurableSet_singleton 0).compl.preimage measurable_snd)
  filter_upwards [hV, ae_weightedRestrictionKernel_eq P μ hm (ball 0 1)
    measurableSet_ball (fun _ => 1) measurable_const] with ω hv he
  have hac : κ ω ≪ μ ω := by
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))
  apply hac.ae_le
  apply ae_iff.mpr
  simpa using (hv.2 1 (by norm_num)).measure_singleton (by simp)

/-- For every positive error tolerance, singular roots sufficiently near the
origin have less than that probability. No polynomial rate is asserted. -/
theorem exists_singular_unitDisc_root_origin_neighborhood_small
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ‖p.2‖ < t} < δ := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  let : IsFiniteKernel κ := weightedRestrictionKernel_finite P μ _ _ _ _ _
  let E : ℕ → Set (Ω × ℂ) := fun n => {p | ‖p.2‖ < 1 / ((n : ℝ) + 1)}
  have hE (n : ℕ) : MeasurableSet (E n) :=
    measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const
  have hlim : ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n in atTop, p ∈ E n ↔ p ∈ (∅ : Set (Ω × ℂ)) := by
    filter_upwards [ae_singular_unitDisc_root_ne_zero hgrowth hγ hγ2 hα h hμ] with p hp
    have hn : 0 < ‖p.2‖ := norm_pos_iff.mpr hp
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hn)] with n hn'
    simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hn'.le
  have ht : Tendsto (fun n => (P ⊗ₘ κ) (E n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim
  obtain ⟨n, hn⟩ := (ht.eventually_lt_const hδ).exists
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

/-- The separated polynomial tail extends to all singular roots up to an
arbitrarily small additive error. The separation radius depends on the error,
and the scale window must fit inside that radius. -/
theorem exists_singular_unitDisc_root_goodAnnuli_tail_with_origin_error
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ≥0∞, 0 < δ → ∃ t : ℝ, 0 < t ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      6 * s * ε ^ (3 / 4 : ℝ) ≤ t →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ δ + ENNReal.ofReal (C * ε ^ q) := by
  obtain ⟨a, ha, ht⟩ := exists_singular_unitDisc_root_separated_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 hα h hμ hμ₀ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro δ hδ
  obtain ⟨t, htpos, hnear⟩ :=
    exists_singular_unitDisc_root_origin_neighborhood_small hgrowth hγ hγ2 hα h hμ hδ
  refine ⟨t, htpos, ?_⟩
  intro ε hε hε1 hlog hsmall
  calc
    _ ≤ (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const) {p | ‖p.2‖ < t} +
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | t ≤ ‖p.2‖ ∧ ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro p hp
      by_cases hz : ‖p.2‖ < t
      · exact Or.inl hz
      · exact Or.inr ⟨le_of_not_gt hz, hp⟩
    _ ≤ δ + ENNReal.ofReal (C * ε ^ q) :=
      add_le_add hnear.le (htail ε t hε hε1 hlog hsmall)

end HarmonicBalls.Section6
