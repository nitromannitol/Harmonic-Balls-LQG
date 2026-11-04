import HarmonicBalls.Proofs.Sec6.DyadicPhaseCriterionProbability
import HarmonicBalls.Proofs.Sec6.SingularDyadicSizeWindows
import HarmonicBalls.Proofs.Sec8.SingularPhaseCriterionComparison

/-! # Very-good annuli for singular fields at dyadic scales

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The logarithmic singularity
is handled by comparison on annuli separated from the origin.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A reference prevalence estimate and volume growth give a uniform
very-good-annulus bound for singular measures at prescribed admissible centres
and inverse dyadic radii. -/
theorem exists_universal_singular_dyadic_veryGood_probability_of_affine
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] (P₀ : Measure Ξ) {γ α β a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β) (ha : 0 < a) (hc : 0 < c)
    {hC₀ : Ξ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ → ℝ → ℂ → ℝ} {ν₀ : Ξ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc →
        ∀ (n : ℕ) (z : ℂ),
        dyadicScale n / 100 ≤ infDist (0 : ℂ)
          (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) →
        P {ω | ¬ IsVeryGoodAnnulus (μ ω) β (dyadicScale n) z N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c} ≤ δ + δ + δ := by
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
    exists_universal_lqg_size_windows_dyadic (α₀ := α) hgrowth hγ hγ₂ hβ P₀ h₀ hν₀ hδ
  obtain ⟨N₀, hN₀, hthree⟩ :=
    exists_universal_dyadic_criterionThree_center_probability_of_affine
      P₀ hγ hc h₀ hν₀ hAff₀ hprev hunit hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hEx hAff n z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have ht := measure_not_phaseVeryGoodCriterionThree_le_of_singular_weight P
    (x₀ := z) (N₀ := N) (phase := fun _ => 0) (a := a) (b := b) (C₃ := c)
    (dyadicScale_pos n) hd (hN₀.trans hN) hweight
  have ht' : P {ω | ¬ VeryGoodCriterionThree (μ ω) (dyadicScale n) z N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b c} ≤ δ := by
    simp only [phaseVeryGoodCriterionThree_zero] at ht
    exact ht.trans (hthree N hN Ω P hC hcirc ν hgff hν hAff n z)
  have hs := hsize Ω P hC hcirc μ hgff hμ hEx hAff n z hd
  exact (measure_not_veryGoodAnnulus_le P μ β (dyadicScale n) z N
    _ b C₁m C₁p C₂m C₂p c).trans (add_le_add (add_le_add hs.1 hs.2) ht')

end HarmonicBalls.Section6
