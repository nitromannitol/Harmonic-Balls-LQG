import HarmonicBalls.Proofs.Sec6.CriterionThreeUniversalLaw
import HarmonicBalls.Proofs.Sec6.SizeRatioScalingLaw
import HarmonicBalls.Proofs.Sec8.GoodRadiusScaling

/-! # Dilation of the third very-good-annulus criterion -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

/-- Multiplying a measure by a finite positive constant preserves criterion
three. -/
theorem criterionThree_smul (μ : Measure ℂ) (ρ : ℝ) (z : ℂ) (N : ℕ)
    (a b c : ℝ) {t : ℝ≥0∞} (ht : t ≠ 0) (htt : t ≠ ∞) :
    VeryGoodCriterionThree (t • μ) ρ z N a b c ↔ VeryGoodCriterionThree μ ρ z N a b c := by
  simp only [VeryGoodCriterionThree, isGoodAnnulus_smul μ _ _ _ _ ht htt]

/-- Inverse dilation transports criterion three between centered annuli. -/
theorem criterionThree_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (ρ : ℝ) (N : ℕ) (a b c : ℝ) :
    VeryGoodCriterionThree (μ.map (fun x : ℂ => k⁻¹ • x)) ρ 0 N a b c ↔
      VeryGoodCriterionThree μ (k * ρ) 0 N a b c := by
  have hp : (fun z : ℂ => k⁻¹ • z) ⁻¹' annulus (0 : ℂ) (ρ / 2) ρ =
      annulus 0 ((k * ρ) / 2) (k * ρ) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
    congr 2; ring
  have hmem (z : ℂ) : z ∈ annulus (0 : ℂ) (ρ / 2) ρ ↔
      k • z ∈ annulus (0 : ℂ) ((k * ρ) / 2) (k * ρ) := by
    rw [← hp]
    simp only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have hinj : Function.Injective (fun z : ℂ => k • z) := by
    intro x y h
    have h' := congrArg (fun z : ℂ => k⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h'
  have hscale (n : ℕ) (j l : ℤ) :
      k • (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) =
        (((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 1
    congr 1
    ring
  have hlat (n : ℕ) (z : ℂ) :
      z ∈ scaledLattice (dyadicScale n * ρ / 100) ↔
      k • z ∈ scaledLattice (dyadicScale n * (k * ρ) / 100) := by
    change (∃ j l : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I)) ↔
      (∃ j l : ℤ, k • z = ((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I))
    constructor
    · rintro ⟨j, l, rfl⟩
      exact ⟨j, l, hscale n j l⟩
    · rintro ⟨j, l, h⟩
      exact ⟨j, l, hinj (h.trans (hscale n j l).symm)⟩
  constructor
  · intro h n hn z hz
    have hz' : k⁻¹ • z ∈ annulus (0 : ℂ) (ρ / 2) ρ := by
      rw [← hp] at hz
      exact hz.2
    have hlat' := (hlat n (k⁻¹ • z)).mpr (by
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hz.1)
    have hh := h n hn (k⁻¹ • z) ⟨hlat', hz'⟩
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n (k⁻¹ • z) a b
      (fun r => isGoodAnnulus_map_inv_smul_iff hk μ r (k⁻¹ • z) a b)] at hh
    simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hh
  · intro h n hn z hz
    have hh := h n hn (k • z) ⟨(hlat n z).mp hz.1, (hmem z).mp hz.2⟩
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n z a b
      (fun r => isGoodAnnulus_map_inv_smul_iff hk μ r z a b)]
    exact hh

/-- The failure probability of criterion three at the origin is independent
of scale, under the affine and coordinate-change inputs. -/
theorem measure_criterionThree_failure_scale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (a b c : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} =
      P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ 0 N a b c} := by
  have hd := hgff.identDistrib_normalizedPullback hAff hCC hγ hγ₂ hα hμ hρ
  have hm := (measurableSet_criterionThree_of_unit_good 1 (by norm_num) 0 N a b c hunit).compl
  have heq := hd.measure_mem_eq hm
  have htransport (ω : Ω) :
      VeryGoodCriterionThree (normalizedPullbackMeasure γ α₀ ρ (hcirc ω) (μ ω))
        1 0 N a b c ↔ VeryGoodCriterionThree (μ ω) ρ 0 N a b c := by
    unfold normalizedPullbackMeasure
    rw [criterionThree_smul _ _ _ _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
      criterionThree_map_inv_smul _ hρ]
    simp only [mul_one]
  change P {ω | ¬ VeryGoodCriterionThree (μ ω) 1 0 N a b c} =
      P {ω | ¬ VeryGoodCriterionThree
        (normalizedPullbackMeasure γ α₀ ρ (hcirc ω) (μ ω)) 1 0 N a b c} at heq
  simpa only [htransport] using heq

universe u

/-- A single starting index controls criterion three at every positive
centered scale in every whole-plane realization. -/
theorem exists_universal_centered_criterionThree_probability
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ}
    {μ₀ : Ω₀ → Measure ℂ} {a b c : ℝ} (hc : 0 < c)
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ ρ : ℝ, 0 < ρ →
        P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ 0 N a b c} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ :=
    exists_universal_unit_criterionThree_probability P₀ hc h₀ hμ₀ hprev hunit hδ
  refine ⟨N₀, hN₀, fun N hN Ω _ P hC hcirc μ hgff hμ hAff hCC ρ hρ => ?_⟩
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  rw [← measure_criterionThree_failure_scale hγ hγ₂ hQ hgff hμ hAff hCC hρ N a b c hunit]
  exact hbound N hN Ω P hC hcirc μ hgff hμ

end HarmonicBalls.Section6
