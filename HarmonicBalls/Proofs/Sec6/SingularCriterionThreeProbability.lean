import HarmonicBalls.Proofs.Sec6.CriterionThreeOffCenterScaling
import HarmonicBalls.Proofs.Sec6.UniversalSizeWindows

/-! # Criterion-three probabilities for a singular field -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A whole-plane prevalence estimate gives a uniform criterion-three
probability for singular fields on annuli separated from the singularity.
The threshold is reduced by the explicit oscillation factor of the Weyl
weight. -/
theorem exists_universal_singular_criterionThree_probability
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
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
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ ρ : ℝ, 0 < ρ → ∀ x : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus x (ρ / 4) (2 * ρ)) →
        P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ x N
          (a / (((401 : ℝ) ^ |-(γ * α₀)|) ^ 2)) b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_universal_criterionThree_probability
    P₀ hγ hγ₂ hc h₀ hμ₀ hAff₀ hCC₀ hprev hunit hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc μ hgff hμ hEx hW hAff hCC ρ hρ x hd => ?_⟩
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  exact (measure_not_criterionThree_le_of_singular_weight P hρ hd (hN₀.trans hN) hweight).trans
    (hbound N hN Ω P hC hcirc ν hgff hν hAff hCC ρ hρ x)

end HarmonicBalls.Section6
