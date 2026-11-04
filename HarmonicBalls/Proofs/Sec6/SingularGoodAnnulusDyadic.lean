import HarmonicBalls.Proofs.Sec6.GoodAnnulusDyadicLaw
import HarmonicBalls.Proofs.Sec6.GoodAnnulusReduction
import HarmonicBalls.Proofs.Sec6.SingularDyadicSizeWindows

/-! # Singular good-annulus probabilities at dyadic scales

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The singularity is
handled by comparison of its deterministic weight away from zero.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A single threshold controls the failure probability of singular-field
annuli at all inverse dyadic scales and all centres separated from zero. -/
theorem exists_universal_singular_goodAnnulus_probability_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc →
      ∀ (n : ℕ) (z : ℂ),
      dyadicScale n / 100 ≤ infDist (0 : ℂ)
        (annulus z (3 * dyadicScale n) (5 * dyadicScale n)) →
      P {ω | ¬ IsGoodAnnulus (μ ω) (dyadicScale n) z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hbound⟩ := exists_universal_goodAnnulus_probability_dyadic
    hgrowth hγ hγ2 h₀ hμ₀ hAff₀ hb hp
  let t : ℝ := (1001 : ℝ) ^ |-(γ * α₀)|
  have ht : 1 ≤ t := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  refine ⟨a / t ^ 2, ⟨div_pos ha.1 (sq_pos_of_pos htpos), ?_⟩, ?_⟩
  · rw [div_lt_one (sq_pos_of_pos htpos)]
    nlinarith [ha.2]
  intro Ω _ P hC hcirc μ hgff hμ hEx hAff n z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ2 hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ2 hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  exact (badGoodAnnulus_measure_le_of_singular_weight P (dyadicScale_pos n) hd hweight).trans
    (hbound Ω P hC hcirc ν hgff hν hAff n z)

/-- The good-annulus condition and both size-window conditions hold together
with high probability, uniformly at admissible inverse dyadic scales. -/
theorem exists_universal_singular_goodAnnulus_size_probability_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ β : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    {b : ℝ} (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc →
        ∀ (n : ℕ) (z : ℂ),
        dyadicScale n / 100 ≤ infDist (0 : ℂ)
          (annulus z (3 * dyadicScale n) (5 * dyadicScale n)) →
        dyadicScale n / 100 ≤ infDist (0 : ℂ)
          (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) →
        P {ω | ¬ (IsGoodAnnulus (μ ω) (dyadicScale n) z a b ∧
          annulusBallMassSize (μ ω) β (dyadicScale n) z /
            (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∈
            Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
          annulusGreenPotentialSup (μ ω) z (dyadicScale n / 4) (2 * dyadicScale n) /
            (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∈
            Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))} ≤
          ENNReal.ofReal (1 - p) + δ + δ := by
  obtain ⟨a, ha, hgood⟩ := exists_universal_singular_goodAnnulus_probability_dyadic
    (α₀ := α₀) hgrowth hγ hγ2 h₀ hμ₀ hAff₀ hb hp
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
    exists_universal_lqg_size_windows_dyadic (α₀ := α₀) hgrowth hγ hγ2 hβ P₀ h₀ hμ₀ hδ
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hEx hAff n z hda hds
  have hg := hgood Ω P hC hcirc μ hgff hμ hEx hAff n z hda
  have hs := hsize Ω P hC hcirc μ hgff hμ hEx hAff n z hds
  let A := {ω | ¬ IsGoodAnnulus (μ ω) (dyadicScale n) z a b}
  let B := {ω | annulusBallMassSize (μ ω) β (dyadicScale n) z /
    (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∉
    Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)}
  let C := {ω | annulusGreenPotentialSup (μ ω) z (dyadicScale n / 4) (2 * dyadicScale n) /
    (μ ω) (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) ∉
    Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)}
  calc
    _ ≤ P A + P B + P C := by
      rw [add_assoc]
      apply (measure_mono (show _ ⊆ A ∪ (B ∪ C) from ?_)).trans
        ((measure_union_le A (B ∪ C)).trans (add_le_add_right (measure_union_le B C) _))
      intro ω hω
      simp only [A, B, C, mem_union, mem_ofPred_eq, not_and_or] at *
      tauto
    _ ≤ ENNReal.ofReal (1 - p) + δ + δ := add_le_add (add_le_add hg hs.1) hs.2

end HarmonicBalls.Section6
