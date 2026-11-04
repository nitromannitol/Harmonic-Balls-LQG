import HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration
import HarmonicBalls.Proofs.Sec6.ExponentialScaleDecay

/-! # Good-annulus counts at a fixed center

The annulus iteration bound uses Leonardo Bonanno's proof of Gwynne–Miller's
lemma through `HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration`, based on
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- At a fixed center, the local annulus events and their single-scale
probability bounds imply a polynomial tail for the subrange radius count. -/
theorem goodAnnulus_subrange_probability (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (μ : Ω → Measure ℂ) (z : ℂ) (a b : ℝ),
      (∀ n : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (3 * ((7 : ℝ)⁻¹ ^ n)) (5 * ((7 : ℝ)⁻¹ ^ n)))
        {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) →
      (∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) →
    ∀ ε : ℝ, 0 < ε → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ := goodAnnulus_geometric_iteration α β hα hβ
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff μ z a b hlocal hprob ε hε ht
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (7 : ℝ))
      (by norm_num) hε 1 (by omega) (by simpa using ht)
  have hK' : Real.logb 7 (ε ^ (-1 : ℝ)) / 16 ≤ (K : ℝ) := by simpa using hK
  have hcount := hiter Ω P hC hcirc hgff μ z a b n₀ ε (ε ^ (3 / 4 : ℝ)) hε
    (fun k => hlocal (n₀ + k)) (fun k => hprob (n₀ + k)) K (by simpa using hrange)
  have hthreshold : (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤ β * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK' hβ.1.le]
  have hsub : {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ⊆
      {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) < β * K} :=
    fun _ h => lt_of_lt_of_le h hthreshold
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := hcount
    _ ≤ _ := ofReal_exp_bound_le_rpow (by norm_num : (1 : ℝ) < 7) hε hα.le
      (by norm_num : (0 : ℝ) < 16) hCpos.le hK'

end HarmonicBalls.Section6
