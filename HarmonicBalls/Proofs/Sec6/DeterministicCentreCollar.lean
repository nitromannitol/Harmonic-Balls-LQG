import HarmonicBalls.Proofs.Sec6.SingularReferenceCollar
import HarmonicBalls.Proofs.Sec6.RootedCollarRescaling

/-! # Collars at deterministic centres

The fixed-centre estimate uses the staged affine and coordinate-change
hypotheses and Leonardo Bonanno's Section 6 iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- For a zero-strength whole-plane field, relative collar failure has the
same probability at every deterministic centre. -/
theorem measure_relativeCollarFailure_translate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (z : ℂ) (r η : ℝ) (d : ℝ≥0∞) :
    P {ω | RelativeCollarFailure (μ ω) r η d} =
      P {ω | d * μ ω (annulus z (3*r) (5*r)) <
        μ ω (annulus z (3*r-η*r) (5*r+η*r) \
          annulus z (3*r+η*r) (5*r-η*r))} := by
  have ht := (identDistrib_translateMeasure h hμ hAff z).measure_mem_eq
    (measurableSet_relativeCollarFailure r η d)
  change P {ω | RelativeCollarFailure (μ ω) r η d} =
    P {ω | RelativeCollarFailure (affineMeasure γ hcirc μ 1 z ω) r η d} at ht
  have he : {ω | RelativeCollarFailure (affineMeasure γ hcirc μ 1 z ω) r η d} =
      {ω | d * μ ω (annulus z (3*r) (5*r)) <
        μ ω (annulus z (3*r-η*r) (5*r+η*r) \
          annulus z (3*r+η*r) (5*r-η*r))} := by
    ext ω
    simp only [mem_ofPred_eq, affineMeasure, norm_one, Real.log_one, mul_zero,
      add_zero, div_one]
    rw [relativeCollarFailure_smul _ _ _ _ _
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top,
      relativeCollarFailure_map_sub]
  rwa [he] at ht

/-- A single relative collar width controls the zero-strength LQG measure at
all positive scales and all deterministic centres. -/
theorem exists_uniform_deterministicCentre_relative_collar
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ (r : ℝ), 0 < r → ∀ z : ℂ,
      P {ω | d * μ ω (annulus z (3*r) (5*r)) <
        μ ω (annulus z (3*r-η*r) (5*r+η*r) \
          annulus z (3*r+η*r) (5*r-η*r))} < q := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨η, hη, hηc, hbound⟩ := exists_singular_reference_uniform_relative_collar
    hgrowth hγ hγ2 hQ h hμ hμ hAff hCC hc hd hq
  refine ⟨η, hη, hηc, ?_⟩
  intro r hr z
  rw [← measure_relativeCollarFailure_translate h hμ hAff z r η d]
  exact hbound r hr

end HarmonicBalls.Section6
