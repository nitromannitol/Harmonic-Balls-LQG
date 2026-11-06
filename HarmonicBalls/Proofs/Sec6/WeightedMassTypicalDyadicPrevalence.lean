import HarmonicBalls.Proofs.Sec6.MassTypicalDyadicPrevalence

/-! # Weighted mass-typical dyadic annulus counts

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- For a prescribed countable family of positive scales, one threshold and
one full-measure set of fields work for every weighted restriction of the
whole-plane LQG measure. The good annuli use the original measure, and the
eventual index may depend on the root and scale. -/
theorem exists_ae_all_weightedMass_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ w : ℂ → ℝ≥0∞,
      ∀ᵐ z ∂((μ ω).withDensity w).restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_ae_lqg_mass_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht] with ω hω
  intro w
  exact ((withDensity_absolutelyContinuous (μ ω) w).restrict (ball 0 1)).ae_le hω


/-- For a prescribed countable family of positive scales, one threshold and
one full-measure set of fields work for every normalized weighted restriction
of the whole-plane LQG measure. The good annuli use the original measure, and the
eventual index may depend on the root and scale. -/
theorem exists_ae_all_normalizedWeightedMass_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ w : ℂ → ℝ≥0∞,
      ∀ᵐ z ∂normalizedRestriction ((μ ω).withDensity w) (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_ae_all_weightedMass_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht] with ω hω
  intro w
  exact Measure.smul_absolutelyContinuous.ae_le (hω w)

end HarmonicBalls.Section6
