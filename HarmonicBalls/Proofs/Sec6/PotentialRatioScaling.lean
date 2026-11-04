import HarmonicBalls.Proofs.Sec6.LQGPotentialRatio

/-!
# Scaling Green-potential ratios

The extrema ratio used in the fine-support argument is invariant when the underlying
measure is multiplied by a positive constant. This is the cancellation needed for the
additive constant in the scale invariance of the whole-plane field.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

/-- Scaling a measure scales its Green potential by the corresponding real factor. -/
theorem greenPotential_smul_measure (O : Set ℂ) (μ : Measure ℂ) (c : ℝ≥0∞) (x : ℂ) :
    greenPotential O (c • μ) x = c.toReal * greenPotential O μ x := by
  exact integral_smul_measure (greenFunction O x) c

/-- The infimum-to-supremum Green-potential ratio is unchanged by multiplication of
its measure by a finite positive constant, including when either extremum is zero. -/
theorem greenPotential_extrema_ratio_smul_measure
    (O K : Set ℂ) (μ : Measure ℂ) (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hctop : c ≠ ⊤) :
    ((⨅ z : K, ENNReal.ofReal (greenPotential O (c • μ) z)) /
      (⨆ z : O, ENNReal.ofReal (greenPotential O (c • μ) z))).toReal =
    ((⨅ z : K, ENNReal.ofReal (greenPotential O μ z)) /
      (⨆ z : O, ENNReal.ofReal (greenPotential O μ z))).toReal := by
  have hc : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  simp_rw [greenPotential_smul_measure, ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hctop]
  rw [← ENNReal.mul_iInf_of_ne hc₀ hctop, ← ENNReal.mul_iSup,
    ENNReal.mul_div_mul_left _ _ hc₀ hctop]

/-- A constant Weyl factor cancels from the Green-potential ratio. -/
theorem greenPotential_extrema_ratio_const_weyl
    (O K : Set ℂ) (μ : Measure ℂ) (γ t : ℝ) :
    ((⨅ z : K, ENNReal.ofReal
        (greenPotential O (μ.withDensity fun _ => ENNReal.ofReal (Real.exp (γ * t))) z)) /
      (⨆ z : O, ENNReal.ofReal
        (greenPotential O (μ.withDensity fun _ => ENNReal.ofReal (Real.exp (γ * t))) z))).toReal =
    ((⨅ z : K, ENNReal.ofReal (greenPotential O μ z)) /
      (⨆ z : O, ENNReal.ofReal (greenPotential O μ z))).toReal := by
  rw [withDensity_const]
  exact greenPotential_extrema_ratio_smul_measure O K μ _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top

/-- If two Green potentials agree up to one positive factor under bijections of the
compact set and the domain, their extrema ratios agree. -/
theorem greenPotential_extrema_ratio_of_equiv
    (O K O' K' : Set ℂ) (μ ν : Measure ℂ) (c : ℝ)
    (hc : 0 < c) (eK : K ≃ K') (eO : O ≃ O')
    (hK : ∀ x : K, greenPotential O μ x = c * greenPotential O' ν (eK x))
    (hO : ∀ x : O, greenPotential O μ x = c * greenPotential O' ν (eO x)) :
    ((⨅ z : K, ENNReal.ofReal (greenPotential O μ z)) /
      (⨆ z : O, ENNReal.ofReal (greenPotential O μ z))).toReal =
    ((⨅ z : K', ENNReal.ofReal (greenPotential O' ν z)) /
      (⨆ z : O', ENNReal.ofReal (greenPotential O' ν z))).toReal := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  simp_rw [hK, hO, ENNReal.ofReal_mul hc.le]
  rw [← ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top, ← ENNReal.mul_iSup,
    ENNReal.mul_div_mul_left _ _ hc0 ENNReal.ofReal_ne_top]
  have hi := eK.iInf_comp (g := fun z : K' => ENNReal.ofReal (greenPotential O' ν z))
  have hs := eO.iSup_comp (g := fun z : O' => ENNReal.ofReal (greenPotential O' ν z))
  rw [hi, hs]

end HarmonicBalls.Section6
