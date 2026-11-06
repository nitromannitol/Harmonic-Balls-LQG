import HarmonicBalls.Proofs.Sec6.WeightedMassTypicalDyadicPrevalence
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure

/-! # Subcritical singular mass-typical annulus counts

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The cofinal existence
assumptions are staged literature inputs pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A single threshold and full-measure field event work for the restricted
mass of every existing subcritical singular limit. Annuli use the original
whole-plane measure; the eventual index may depend on the root and scale. -/
theorem exists_ae_all_subcritical_mass_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) ν →
      ∀ᵐ z ∂ν.restrict (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => h.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  obtain ⟨a, ha, ht⟩ := exists_ae_all_weightedMass_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht, hμ, hc,
    ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc h hE]
    with ω hw hm hc hno α hα ν hn
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) :=
    fun f hf => isLQGLimit_addCircleAverage hm hc f hf
  have heq := eq_singularWeight_of_origin_nonatomic hn hW (hno α hα ν hn)
    (hno 0 hQ (μ ω) hm)
  rw [heq]
  exact hw _


/-- A single threshold and full-measure field event work for the normalized
restriction of every existing subcritical singular limit. Annuli use the original
whole-plane measure; the eventual index may depend on the root and scale. -/
theorem exists_ae_all_subcritical_normalizedMass_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) ν →
      ∀ᵐ z ∂normalizedRestriction ν (ball 0 1), ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) z a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_ae_all_subcritical_mass_eventually_dyadic_goodAnnuli_count_all_scales
    hgrowth hγ hγ2 h hμ hE hb β hβ s hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht] with ω hω
  intro α hα ν hn
  exact Measure.smul_absolutelyContinuous.ae_le (hω α hα ν hn)

end HarmonicBalls.Section6
