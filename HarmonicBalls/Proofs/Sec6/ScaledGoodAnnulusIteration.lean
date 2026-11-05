import HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration
import HarmonicBalls.Proofs.Sec6.ExponentialScaleDecay

/-! # Annulus iteration at scaled seven-adic radii

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Uniform local events at `s * 7⁻ⁿ` give a polynomial lower-tail bound
for the count of their normalized radii in a three-quarter subrange. The
iteration constants do not depend on the positive scale factor `s`. -/
theorem scaled_goodAnnulus_subrange_probability (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (μ : Ω → Measure ℂ) (z : ℂ) (a b s : ℝ), 0 < s →
      (∀ n : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (3 * (s * ((7 : ℝ)⁻¹ ^ n))) (5 * (s * ((7 : ℝ)⁻¹ ^ n))))
        {ω | IsGoodAnnulus (μ ω) (s * ((7 : ℝ)⁻¹ ^ n)) z a b}) →
      (∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsGoodAnnulus (μ ω) (s * ((7 : ℝ)⁻¹ ^ n)) z a b}) →
    ∀ ε : ℝ, 0 < ε → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) (s * r) z a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulusIterationStmt_proved (3 / 7) (5 / 7) (by norm_num) (by norm_num)
      (by norm_num) α hα β hβ
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff μ z a b s hs hlocal hprob ε hε ht
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (7 : ℝ))
      (by norm_num) hε 1 (by omega) (by simpa using ht)
  have hK' : Real.logb 7 (ε ^ (-1 : ℝ)) / 16 ≤ (K : ℝ) := by simpa using hK
  let r : ℕ → ℝ := fun k => 7 * s * (7 : ℝ)⁻¹ ^ (n₀ + k)
  let E : ℕ → Set Ω := fun k => {ω | IsGoodAnnulus (μ ω)
    (s * (7 : ℝ)⁻¹ ^ (n₀ + k)) z a b}
  have hr : ∀ k, 0 < r k := fun k => by dsimp [r]; positivity
  have hratio : ∀ k, r (k + 1) ≤ (3 / 7 : ℝ) * r k := by
    intro k
    dsimp [r]
    rw [show n₀ + (k + 1) = (n₀ + k) + 1 by omega, pow_succ]
    have hpw : 0 ≤ (7 : ℝ)⁻¹ ^ (n₀ + k) := by positivity
    nlinarith
  have hloc : ∀ k, IsFieldMeasurableModConst P 0 hC
      (annulus 0 ((3 / 7 : ℝ) * r k) ((5 / 7 : ℝ) * r k)) (E k) := by
    intro k
    convert hlocal (n₀ + k) using 1
    all_goals dsimp [r, E]
    all_goals congr 1
    all_goals ring
  have hbound := hiter 0 Ω P hC hcirc hgff r hr hratio E hloc
    (fun k => hprob (n₀ + k)) K
  have hcount : P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus (μ ω) (s * r) z a b}.ncard : ℝ)
        < β * K} ≤ ENNReal.ofReal (C * Real.exp (-α * K)) := by
    apply (measure_mono ?_).trans hbound
    intro ω hω
    have h := geometric_scale_count_le (by norm_num : (0 : ℝ) < 7⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ < 1) hε
      (fun t => IsGoodAnnulus (μ ω) (s * t) z a b) n₀ 1 K (by omega) hrange
    simp only [one_mul] at h
    change (((Finset.range K).filter fun k => IsGoodAnnulus (μ ω)
      (s * (7 : ℝ)⁻¹ ^ (n₀ + k)) z a b).card : ℝ) < β * K
    exact lt_of_le_of_lt (by exact_mod_cast h) hω
  have hthreshold : (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤ β * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK' hβ.1.le]
  calc
    _ ≤ _ := measure_mono (fun _ h => lt_of_lt_of_le h hthreshold)
    _ ≤ _ := hcount
    _ ≤ _ := ofReal_exp_bound_le_rpow (by norm_num : (1 : ℝ) < 7) hε hα.le
      (by norm_num : (0 : ℝ) < 16) hCpos.le hK'

end HarmonicBalls.Section6
