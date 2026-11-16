import HarmonicBalls.Proofs.GFF.QuadraticCrossingNormalization

/-! # All-scale quadratic crossing bounds

The simultaneous crossing-ratio bounds are incompatible at all positive scales
when the Weyl parameter is positive.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- Positive exponential growth eventually exceeds any finite ratio bound. -/
theorem exists_quadratic_exp_mul_gt {ξ a b : ℝ} (hξ : 0 < ξ) (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ b < Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2) * a := by
  let c : ℝ := (12 / 5 : ℝ) * ξ
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨r, hr⟩ := exists_gt (max 1 (b / a / c))
  have hr1 : 1 < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrb : b / a / c < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hcr : b / a < c * r := by simpa [mul_comm] using (div_lt_iff₀ hc).mp hrb
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hcr2 : c * r ≤ c * r ^ 2 := mul_le_mul_of_nonneg_left hr2 hc.le
  have hexp := Real.add_one_le_exp (c * r ^ 2)
  have hreal : b < Real.exp (c * r ^ 2) * a := by
    have : b < (c * r ^ 2) * a := (div_lt_iff₀ ha).mp (lt_of_lt_of_le hcr hcr2)
    nlinarith
  exact ⟨r, by linarith, hreal⟩

/-- The quantitative crossing-ratio bounds cannot hold at every positive scale. -/
theorem quadraticCrossingFamily_not_all_scale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {ξ : ℝ}
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hpointD : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hpointE : ∀ x y, AEMeasurable (fun ω => E ω x y) P)
    (hN : ∀ r, 0 < r → AEMeasurable (N r) P)
    (hK : ∀ r, 0 < r → AEMeasurable (K r) P)
    (hNfinite : ∀ r, 0 < r → ∀ᵐ ω ∂P, N r ω ≠ 0 ∧ N r ω ≠ ⊤)
    (hKfinite : ∀ r, 0 < r → ∀ᵐ ω ∂P, K r ω ≠ 0 ∧ K r ω ≠ ⊤)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily D E N K i)) :
    False := by
  obtain ⟨M, hM, hbound⟩ := quadraticCrossingFamily_ratio_simultaneous
    hξ hD hE hpointD hpointE hN hK hNfinite hKfinite hscale htight
    (ε := 1 / 2) (by norm_num) (by norm_num)
  let a : ℝ := (M 0)⁻¹ / M 1
  let b : ℝ := M 2 / (M 3)⁻¹
  have ha : 0 < a := div_pos (inv_pos.mpr (hM 0)) (hM 1)
  obtain ⟨r, hr, hlarge⟩ := exists_quadratic_exp_mul_gt hξ ha (b := b)
  have hlarge' : ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹ <
      ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
        (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) := by
    rw [← ENNReal.ofReal_div_of_pos (hM 1),
      ← ENNReal.ofReal_div_of_pos (inv_pos.mpr (hM 3)),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos (Real.exp_pos _) ha)).2 hlarge
  have hempty : {ω | ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
        (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
      quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ∧
    quadraticCrossingFamily D E N K 2 r ω / quadraticCrossingFamily D E N K 3 r ω ≤
      ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (not_le_of_gt hlarge') (hω.1.trans hω.2)
  have h := hbound r hr
  rw [hempty, measure_empty] at h
  have hp : (0 : ℝ≥0∞) < ENNReal.ofReal (1 - 1 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
  exact (not_le_of_gt hp) h

end HarmonicBalls
