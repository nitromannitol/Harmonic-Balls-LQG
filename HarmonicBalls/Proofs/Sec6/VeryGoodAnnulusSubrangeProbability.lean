import HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration
import HarmonicBalls.Proofs.Sec6.ExponentialScaleDecay

/-! # Very-good annulus counts at a fixed center

The annulus iteration bound uses Leonardo Bonanno's proof of Gwynne–Miller's
lemma through `HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration`, based on
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.

Locality and single-scale probability are assumed for the actual absolute
lattice in the very-good event, without a translation of its lattice phase.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- At a fixed center, local very-good annulus events and their single-scale
probability bounds imply a polynomial tail for the subrange radius count. -/
theorem veryGoodAnnulus_subrange_probability (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (μ : Ω → Measure ℂ) (z : ℂ) (βminus : ℝ) (N : ℕ)
      (a b C₁m C₁p C₂m C₂p C₃ : ℝ),
      (∀ n : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (((8 : ℝ)⁻¹ ^ n) / 4) (2 * ((8 : ℝ)⁻¹ ^ n)))
        {ω | IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ n) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
      (∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ n) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
    ∀ ε : ℝ, 0 < ε → 32 ≤ Real.logb 8 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
        IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) <
        (β / 32) * Real.logb 8 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (32 * Real.log 8))) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ := veryGoodAnnulus_geometric_iteration α β hα hβ
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff μ z βminus N a b C₁m C₁p C₂m C₂p C₃ hlocal hprob ε hε ht
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (8 : ℝ))
      (by norm_num) hε 2 (by omega) (by norm_num; exact ht)
  have hK' : Real.logb 8 (ε ^ (-1 : ℝ)) / 32 ≤ (K : ℝ) := by
    norm_num at hK ⊢
    exact hK
  have hcount := hiter Ω P hC hcirc hgff μ z βminus N a b C₁m C₁p C₂m C₂p C₃
    n₀ ε (ε ^ (3 / 4 : ℝ)) hε (fun k => hlocal (n₀ + 2 * k))
    (fun k => hprob (n₀ + 2 * k)) K hrange
  have hthreshold : (β / 32) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤ β * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK' hβ.1.le]
  have hsub : {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
      IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) <
        (β / 32) * Real.logb 8 (ε ^ (-1 : ℝ))} ⊆
      {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
      IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ) < β * K} :=
    fun _ h => lt_of_lt_of_le h hthreshold
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := hcount
    _ ≤ _ := ofReal_exp_bound_le_rpow (by norm_num : (1 : ℝ) < 8) hε hα.le
      (by norm_num : (0 : ℝ) < 32) hCpos.le hK'

end HarmonicBalls.Section6
