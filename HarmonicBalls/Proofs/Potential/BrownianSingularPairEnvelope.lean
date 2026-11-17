import HarmonicBalls.Proofs.Potential.BrownianSingularPairHolder

/-! # Singular Brownian pair envelopes

A geometric sum of near-diagonal occupations has finite Brownian expectation.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The singularly weighted occupation of pairs at distance less than `r`. -/
noncomputable def unitSingularPairNear (z : ℂ) (q r : ℝ) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  ∫⁻ p : ℝ≥0 × ℝ≥0,
    (if ‖b p.1 - b p.2‖ < r then
      (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
        (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) else 0) ∂(ν.prod ν)

/-- The near-diagonal pair occupation is measurable in the path. -/
theorem measurable_unitSingularPairNear (z : ℂ) (q r : ℝ) :
    Measurable (unitSingularPairNear z q r) := by
  have hE : MeasurableSet {v : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) |
      ‖v.1 v.2.1 - v.1 v.2.2‖ < r} := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  have hf : Measurable (fun v : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q) *
        (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q)) := by fun_prop
  have hi : Measurable (fun v : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      if ‖v.1 v.2.1 - v.1 v.2.2‖ < r then
        (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q) *
          (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q) else 0) := by
    convert hf.indicator hE using 1
    funext v
    by_cases hv : ‖v.1 v.2.1 - v.1 v.2.2‖ < r <;> simp [hv]
  exact hi.lintegral_prod_right

/-- A geometric sum of dyadic singular pair occupations. -/
noncomputable def unitSingularPairDyadicEnvelope (z : ℂ) (q d : ℝ)
    (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ d) ^ n *
    unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ n) b

/-- The dyadic envelope is measurable in the path. -/
theorem measurable_unitSingularPairDyadicEnvelope (z : ℂ) (q d : ℝ) :
    Measurable (unitSingularPairDyadicEnvelope z q d) := by
  unfold unitSingularPairDyadicEnvelope
  exact Measurable.tsum fun n => measurable_const.mul
    (measurable_unitSingularPairNear z q _)

/-- The dyadic envelope has finite expectation below the expected pair exponent. -/
theorem planarBrownianMotion_unit_singular_pair_dyadic_envelope_lt_top
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd : d < β * (1 - q/q₂)) :
    (∫⁻ b, unitSingularPairDyadicEnvelope z q d b ∂(planarBrownianMotion x)) < ∞ := by
  let κ := β * (1 - q/q₂)
  obtain ⟨C, hC, hbound⟩ := planarBrownianMotion_unit_singular_pair_near_le x z hq hqq hq₂ hβ hβ₂
  let a : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ d)
  let t : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ)⁻¹) ^ κ)
  have hbase : a * t < 1 := by
    dsimp [a, t]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_lt_one.mpr
    rw [show ((2 : ℝ)⁻¹) ^ κ = (2 : ℝ) ^ (-κ) by rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]]
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by dsimp [κ]; linarith)
  have hpow (n : ℕ) : ENNReal.ofReal ((((2 : ℝ)⁻¹) ^ n) ^ κ) = t ^ n := by
    dsimp [t]
    rw [← Real.rpow_natCast_mul (by norm_num) n κ,
      show (n : ℝ) * κ = κ * n by ring, Real.rpow_mul_natCast (by norm_num),
      ENNReal.ofReal_pow (by positivity)]
  unfold unitSingularPairDyadicEnvelope
  rw [lintegral_tsum (f := fun n b => ENNReal.ofReal ((2 : ℝ) ^ d) ^ n *
    unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ n) b)
    (fun n => (measurable_const.mul (measurable_unitSingularPairNear z q _)).aemeasurable)]
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top hC (tsum_geometric_lt_top.mpr hbase))
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  rw [lintegral_const_mul' _ _ (by simp)]
  calc
    _ ≤ a ^ n * (C * t ^ n) := by
      gcongr
      have hb := hbound (((2 : ℝ)⁻¹) ^ n) (by positivity)
      change (∫⁻ b, unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ n) b
        ∂(planarBrownianMotion x)) ≤ C * ENNReal.ofReal ((((2 : ℝ)⁻¹) ^ n) ^ κ) at hb
      rw [hpow n] at hb
      exact hb
    _ = C * (a * t) ^ n := by rw [mul_pow]; ac_rfl

/-- The real-valued dyadic envelope, defined by taking the finite part of the series. -/
noncomputable def unitSingularPairDyadicEnvelopeReal (z : ℂ) (q d : ℝ)
    (b : ContinuousPath ℂ) : ℝ := (unitSingularPairDyadicEnvelope z q d b).toReal

/-- The dyadic envelope is integrable under planar Brownian motion. -/
theorem integrable_unitSingularPairDyadicEnvelopeReal
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd : d < β * (1 - q/q₂)) :
    Integrable (unitSingularPairDyadicEnvelopeReal z q d) (planarBrownianMotion x) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (measurable_unitSingularPairDyadicEnvelope z q d).aemeasurable
  · exact (planarBrownianMotion_unit_singular_pair_dyadic_envelope_lt_top
      x z hq hqq hq₂ hβ hβ₂ hd).ne

/-- On one Brownian full-measure event, the envelope controls every dyadic term. -/
theorem planarBrownianMotion_ae_unit_singular_pair_dyadic_le
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd : d < β * (1 - q/q₂)) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ n : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ d) ^ n *
        unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ n) b ≤
      ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) := by
  filter_upwards [ae_lt_top (measurable_unitSingularPairDyadicEnvelope z q d)
    (planarBrownianMotion_unit_singular_pair_dyadic_envelope_lt_top
      x z hq hqq hq₂ hβ hβ₂ hd).ne] with b hb
  intro n
  rw [unitSingularPairDyadicEnvelopeReal, ENNReal.ofReal_toReal hb.ne]
  unfold unitSingularPairDyadicEnvelope
  exact ENNReal.le_tsum (f := fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ d) ^ k *
    unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ k) b) n

end HarmonicBalls
