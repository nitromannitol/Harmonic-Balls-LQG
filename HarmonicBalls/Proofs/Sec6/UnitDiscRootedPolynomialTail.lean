import HarmonicBalls.Proofs.Sec6.RootedPolynomialAnnulusTail
import HarmonicBalls.Proofs.Sec8.RawRootedApproximation

/-! # Annulus-count tails under unit-disc LQG sampling

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The unit-disc LQG mass is almost surely positive and finite. -/
theorem ae_unitDisc_lqg_mass_pos_ne_top
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, μ ω (ball 0 1) ≠ 0 ∧ μ ω (ball 0 1) ≠ ∞ := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hf := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
    Ω P hC hcirc μ h hμ
  have hfc : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  have hμ' : IsLQGMeasure P γ hcirc μ := by
    simpa only [IsLQGMeasureOfField, hfc] using hμ
  filter_upwards [hf, hμ'] with ω hfull hlocal
  let : IsLocallyFiniteMeasure (μ ω) := hlocal.isLocallyFiniteMeasure
  exact ⟨(hfull _ isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩).ne', measure_ball_ne_top⟩

/-- A root sampled from normalized LQG mass on the unit disc has a polynomial
lower tail for its number of good annuli, at every fixed positive scale. -/
theorem exists_unitDisc_lqg_root_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hm := h.aemeasurable_lqgMeasure hμ
  let κ := weightedRestrictionKernel P μ hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using ae_unitDisc_lqg_mass_pos_ne_top hgrowth hγ hγ2 h hμ
  have hk : ∀ᵐ ω ∂P, κ ω univ = 1 := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const, hmass] with ω he hh
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hh.1 hh.2
  have hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const] with ω he
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))
  obtain ⟨a, ha, ht⟩ := exists_rooted_unitDisc_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 h hμ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 hlog
  calc
    _ ≤ (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono_ae
      filter_upwards [ae_mem_weightedRestriction_compProd P μ hm (ball 0 1)
        measurableSet_ball (fun _ => 1) measurable_const] with p hp hpE
      exact ⟨hp, hpE⟩
    _ ≤ _ := htail κ hk hac ε hε hε1 hlog

end HarmonicBalls.Section6
