import HarmonicBalls.Proofs.Sec6.UnitDiscRootedDyadicPrevalence

/-! # Mass-typical dyadic annulus counts

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- An almost-everywhere statement under normalized unit-disc LQG sampling
holds for almost every field and almost every root under its restricted mass. -/
theorem ae_restrict_unitDisc_of_ae_lqg_root
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {p : Ω × ℂ → Prop}
    (hp : ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const), p x) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1), p (ω, z) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hsection := Measure.ae_ae_of_ae_compProd hp
  filter_upwards [hsection, ae_unitDisc_lqg_mass_pos_ne_top hgrowth hγ hγ2 h hμ,
    ae_weightedRestrictionKernel_eq P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const] with ω hh hm he
  rw [he, normalizedRestriction, withDensity_const, one_smul] at hh
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hm.2)).mp hh

/-- For a prescribed countable family of positive scales, almost every field
has the eventual dyadic-window count bound at mass-almost-every root in the
unit disc, with a threshold independent of the scale. -/
theorem exists_ae_lqg_mass_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      ∀ᵐ z ∂(μ ω).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_ae_unitDisc_root_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hb β hβ s hs
  exact ⟨a, ha, ae_restrict_unitDisc_of_ae_lqg_root hgrowth hγ hγ2 h hμ ht⟩

end HarmonicBalls.Section6
