import HarmonicBalls.Proofs.Sec6.ScaledPhaseCriterionUniformProbability
import HarmonicBalls.Proofs.Sec8.SingularPhaseCriterionComparison
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Phase criterion for singular LQG measures

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The third criterion for singular measures has a failure bound uniform
in the positive radius, separated centre, and prescribed phase sequence. -/
theorem exists_universal_singular_phaseCriterion_probability_all_radii
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) → ∀ phase : ℕ → ℂ,
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) phase} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hthree⟩ :=
    exists_universal_phaseCriterionThree_probability_all_radii hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd phase
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hE0 hgff hγ hγ₂ hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  exact (measure_not_phaseVeryGoodCriterionThree_le_of_singular_weight P
    (a := a) (b := b) (C₃ := 1 / 32) (phase := phase) hs hd (hN₀.trans hN) hweight).trans
      (hthree N hN Ω P hC hcirc ν hgff hν s hs x phase)

end HarmonicBalls.Section6
