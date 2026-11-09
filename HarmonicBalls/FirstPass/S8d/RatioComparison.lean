import HarmonicBalls.FirstPass.S8d.CriteriaComparison

/-! # FIRST-PASS helper (fp-S8d, owner n4): ratio and Green-potential comparison under a density

Continuation of `CriteriaComparison.lean`. Under `c₁ • lam|_D ≤ μ|_D ≤ c₂ • lam|_D` on the annulus `D = 𝔸_{ρ/4,2ρ}(x₀)`:

* `ratio_transfer`: if `x / y ∈ [C₁, C₂]` and the numerator and denominator are comparable up to `k₁, k₂`, then the
  quotient for the singular measure lies in `[C₁ k₁/k₂, C₂ k₂/k₁]`. This is criteria (VG-i) and (VG-ii) of
  `IsVeryGoodAnnulus` (Defs/Annuli.lean:81).
* `annulusGreenPotentialSup_comparable`: the Green potential supremum `annulusGreenPotentialSup` (Defs/Annuli.lean:65)
  is comparable with the same constants: it is a supremum of integrals of the Green kernel against the restriction to `D`.

No new mathematics. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- Ratio comparison: `x'/y'` lies in `[C₁ k₁/k₂, C₂ k₂/k₁]` when `x/y ∈ [C₁, C₂]`, `x' ∈ [k₁ x, k₂ x]` and
`y' ∈ [k₁ y, k₂ y]`. -/
theorem ratio_transfer (x y x' y' : ℝ≥0∞) (k₁ k₂ C₁ C₂ : ℝ) (hk₁ : 0 < k₁) (hk₁₂ : k₁ ≤ k₂)
    (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂) (hx : x / y ∈ Icc (ENNReal.ofReal C₁) (ENNReal.ofReal C₂))
    (hxl : ENNReal.ofReal k₁ * x ≤ x') (hxu : x' ≤ ENNReal.ofReal k₂ * x)
    (hyl : ENNReal.ofReal k₁ * y ≤ y') (hyu : y' ≤ ENNReal.ofReal k₂ * y) :
    x' / y' ∈ Icc (ENNReal.ofReal (C₁ * (k₁ / k₂))) (ENNReal.ofReal (C₂ * (k₂ / k₁))) := by
  have hk₂ : 0 < k₂ := lt_of_lt_of_le hk₁ hk₁₂
  have hk₂ne : k₂ ≠ 0 := hk₂.ne'
  have hk₁ne : k₁ ≠ 0 := hk₁.ne'
  obtain ⟨hy0, hyT⟩ := denom_pos_finite_of_mem_Icc x y C₁ C₂ hC₁ hx
  have hx2 := (div_mem_Icc_iff_mul x y _ _ hy0 hyT).1 hx
  have hy'0 : y' ≠ 0 := by
    intro h
    rw [h] at hyl
    have h0 : ENNReal.ofReal k₁ * y = 0 := le_zero_iff.1 hyl
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact (ENNReal.ofReal_pos.2 hk₁).ne' h1
    · exact hy0 h1
  have hy'T : y' ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hyT) hyu
  rw [div_mem_Icc_iff_mul x' y' _ _ hy'0 hy'T]
  have e1 : ENNReal.ofReal (C₁ * (k₁ / k₂)) * ENNReal.ofReal k₂ = ENNReal.ofReal k₁ * ENNReal.ofReal C₁ := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hC₁.le (div_nonneg hk₁.le hk₂.le)),
      ← ENNReal.ofReal_mul hk₁.le]
    congr 1
    field_simp
  have e2 : ENNReal.ofReal k₂ * ENNReal.ofReal C₂ = ENNReal.ofReal (C₂ * (k₂ / k₁)) * ENNReal.ofReal k₁ := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hC₂ (div_nonneg hk₂.le hk₁.le)),
      ← ENNReal.ofReal_mul hk₂.le]
    congr 1
    field_simp
  constructor
  · calc ENNReal.ofReal (C₁ * (k₁ / k₂)) * y'
        ≤ ENNReal.ofReal (C₁ * (k₁ / k₂)) * (ENNReal.ofReal k₂ * y) := by gcongr
      _ = ENNReal.ofReal k₁ * (ENNReal.ofReal C₁ * y) := by
          rw [← mul_assoc, e1, mul_assoc]
      _ ≤ ENNReal.ofReal k₁ * x := mul_le_mul_of_nonneg_left hx2.1 zero_le
      _ ≤ x' := hxl
  · calc x' ≤ ENNReal.ofReal k₂ * x := hxu
      _ ≤ ENNReal.ofReal k₂ * (ENNReal.ofReal C₂ * y) := mul_le_mul_of_nonneg_left hx2.2 zero_le
      _ = ENNReal.ofReal (C₂ * (k₂ / k₁)) * (ENNReal.ofReal k₁ * y) := by
          rw [← mul_assoc, e2, mul_assoc]
      _ ≤ ENNReal.ofReal (C₂ * (k₂ / k₁)) * y' := by gcongr

/-- The Green potential supremum is comparable with the constants of the density comparison. -/
theorem annulusGreenPotentialSup_comparable (lam μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ) (c₁ c₂ : ℝ≥0∞)
    (hlow : c₁ • lam.restrict (annulus x₀ a b) ≤ μ.restrict (annulus x₀ a b))
    (hup : μ.restrict (annulus x₀ a b) ≤ c₂ • lam.restrict (annulus x₀ a b)) :
    c₁ * annulusGreenPotentialSup lam x₀ a b ≤ annulusGreenPotentialSup μ x₀ a b ∧
      annulusGreenPotentialSup μ x₀ a b ≤ c₂ * annulusGreenPotentialSup lam x₀ a b := by
  unfold annulusGreenPotentialSup
  constructor
  · simp only [ENNReal.mul_iSup]
    refine iSup_mono fun x => iSup_mono fun hx => ?_
    rw [← smul_eq_mul, ← lintegral_smul_measure]
    exact lintegral_mono' hlow le_rfl
  · simp only [ENNReal.mul_iSup]
    refine iSup_mono fun x => iSup_mono fun hx => ?_
    rw [← smul_eq_mul, ← lintegral_smul_measure]
    exact lintegral_mono' hup le_rfl

#print axioms ratio_transfer
#print axioms annulusGreenPotentialSup_comparable

end HarmonicBalls
