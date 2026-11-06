import HarmonicBalls.Proofs.Sec6.SingularWeightedRootNormalization

/-! # Singular-weight rooted annulus tails

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Powers of the distance to the origin are Borel measurable, including
at the origin and for negative exponents. -/
theorem measurable_ofReal_norm_rpow (p : ℝ) :
    Measurable (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ p)) := by
  classical
  have hm : Measurable (fun z : ℂ => if z = 0 then ENNReal.ofReal ((0 : ℝ) ^ p)
      else ENNReal.ofReal (Real.exp (Real.log ‖z‖ * p))) :=
    Measurable.ite (measurableSet_singleton 0) measurable_const
      ((Real.measurable_log.comp measurable_id.norm |>.mul_const p |>.exp).ennreal_ofReal)
  convert hm using 1
  ext z
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ite_false, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- The fixed-threshold polynomial tail holds under all subcritical singular
root weights for which the staged existence hypothesis is available. The
threshold and scale-dependent constant do not depend on the singularity. The
good annuli are evaluated for the original whole-plane measure. -/
theorem exists_singularWeighted_unitDisc_root_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ α : ℝ, α < lqgQ γ → LQGMeasureExistence P γ α hC hcirc →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))
        (measurable_ofReal_norm_rpow (-(γ * α))))
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  obtain ⟨a, ha, ht⟩ := exists_weighted_unitDisc_lqg_root_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 h hμ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, ht⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro α hα hE ε hε hε1 hlog
  exact ht _ (measurable_ofReal_norm_rpow _)
    (ae_subcritical_singularWeight_unitDisc_mass_pos_ne_top hgrowth hγ hγ2 hα h hμ hE)
    ε hε hε1 hlog


/-- The fixed-threshold polynomial tail holds simultaneously over the weights
for nonpositive singularities, without a separate existence hypothesis. The
threshold and scale-dependent constant do not depend on the singularity. The
good annuli are evaluated for the original whole-plane measure. -/
theorem exists_weaker_singularWeighted_unitDisc_root_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ α : ℝ, α ≤ 0 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))
        (measurable_ofReal_norm_rpow (-(γ * α))))
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  obtain ⟨a, ha, ht⟩ := exists_weighted_unitDisc_lqg_root_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 h hμ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, ht⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro α hα ε hε hε1 hlog
  exact ht _ (measurable_ofReal_norm_rpow _)
    (ae_weaker_singularWeight_unitDisc_mass_pos_ne_top hgrowth hγ hγ2 hα h hμ)
    ε hε hε1 hlog

end HarmonicBalls.Section6
