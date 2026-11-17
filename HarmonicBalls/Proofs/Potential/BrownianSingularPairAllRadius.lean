import HarmonicBalls.Proofs.Potential.BrownianSingularPairEnvelope

/-! # Singular Brownian pair occupation at arbitrary radii

An integrable pathwise envelope controls singular pair occupations at all positive radii.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The unrestricted singularly weighted occupation of pairs. -/
noncomputable def unitSingularPairOccupation (z : ℂ) (q : ℝ) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  ∫⁻ p : ℝ≥0 × ℝ≥0,
    (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
      (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) ∂(ν.prod ν)

/-- Unrestricted singular pair occupation is measurable in the path. -/
theorem measurable_unitSingularPairOccupation (z : ℂ) (q : ℝ) :
    Measurable (unitSingularPairOccupation z q) := by
  unfold unitSingularPairOccupation
  apply Measurable.lintegral_prod_right
  fun_prop

/-- Near-diagonal occupation increases with the radius. -/
theorem unitSingularPairNear_mono (z : ℂ) (q : ℝ) (b : ContinuousPath ℂ)
    {r s : ℝ} (hrs : r ≤ s) : unitSingularPairNear z q r b ≤ unitSingularPairNear z q s b := by
  unfold unitSingularPairNear
  apply lintegral_mono
  intro p
  dsimp only
  split_ifs with hr hs hs
  · exact le_rfl
  · exact (hs (lt_of_lt_of_le hr hrs)).elim
  · exact bot_le
  · exact le_rfl

/-- A near-diagonal occupation is bounded by the unrestricted occupation. -/
theorem unitSingularPairNear_le_occupation (z : ℂ) (q r : ℝ) (b : ContinuousPath ℂ) :
    unitSingularPairNear z q r b ≤ unitSingularPairOccupation z q b := by
  unfold unitSingularPairNear unitSingularPairOccupation
  apply lintegral_mono
  intro p
  dsimp only
  split_ifs <;> simp

/-- The real part of unrestricted singular pair occupation. -/
noncomputable def unitSingularPairOccupationReal (z : ℂ) (q : ℝ)
    (b : ContinuousPath ℂ) : ℝ := (unitSingularPairOccupation z q b).toReal

/-- Unrestricted singular pair occupation is integrable for `0 < q < 1`. -/
theorem integrable_unitSingularPairOccupationReal (x z : ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    Integrable (unitSingularPairOccupationReal z q) (planarBrownianMotion x) := by
  apply integrable_toReal_of_lintegral_ne_top
  · exact (measurable_unitSingularPairOccupation z q).aemeasurable
  · exact (planarBrownianMotion_unit_singular_pair_occupation_lt_top x z hq0 hq1).ne

/-- A real-valued envelope for all singular pair occupations. -/
noncomputable def unitSingularPairAllRadiusEnvelope (z : ℂ) (q d : ℝ)
    (b : ContinuousPath ℂ) : ℝ :=
  (2 : ℝ) ^ d * unitSingularPairDyadicEnvelopeReal z q d b +
    unitSingularPairOccupationReal z q b

/-- The all-radius envelope is integrable. -/
theorem integrable_unitSingularPairAllRadiusEnvelope
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd : d < β * (1 - q/q₂)) :
    Integrable (unitSingularPairAllRadiusEnvelope z q d) (planarBrownianMotion x) := by
  exact ((integrable_unitSingularPairDyadicEnvelopeReal x z hq hqq hq₂ hβ hβ₂ hd).const_mul _).add
    (integrable_unitSingularPairOccupationReal x z hq (lt_trans hqq hq₂))

/-- For almost every Brownian path, one integrable envelope controls all radii. -/
theorem planarBrownianMotion_ae_unit_singular_pair_all_radius_le
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - q/q₂)) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear z q r b ≤
        ENNReal.ofReal (unitSingularPairAllRadiusEnvelope z q d b) * ENNReal.ofReal (r ^ d) := by
  filter_upwards [planarBrownianMotion_ae_unit_singular_pair_dyadic_le
      x z hq hqq hq₂ hβ hβ₂ hd,
    ae_lt_top (measurable_unitSingularPairOccupation z q)
      (planarBrownianMotion_unit_singular_pair_occupation_lt_top x z hq (lt_trans hqq hq₂)).ne]
    with b hdy hocc r hr
  have hA : 0 ≤ unitSingularPairDyadicEnvelopeReal z q d b := ENNReal.toReal_nonneg
  have hW : 0 ≤ unitSingularPairOccupationReal z q b := ENNReal.toReal_nonneg
  have hR : 0 ≤ r ^ d := (Real.rpow_pos_of_pos hr _).le
  have htwo : 0 ≤ (2 : ℝ) ^ d := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsplit : ENNReal.ofReal (unitSingularPairAllRadiusEnvelope z q d b) =
      ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) +
      ENNReal.ofReal (unitSingularPairOccupationReal z q b) := by
    rw [unitSingularPairAllRadiusEnvelope, ENNReal.ofReal_add (mul_nonneg htwo hA) hW,
      ENNReal.ofReal_mul htwo]
  rw [hsplit, add_mul]
  by_cases hr1 : r ≤ 1
  · obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hr hr1
      (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num) (by norm_num)
    have hscale : ((2 : ℝ)⁻¹) ^ n ≤ 2 * r := by
      rw [pow_succ] at hnlo
      linarith
    have hscale' := Real.rpow_le_rpow (show 0 ≤ ((2 : ℝ)⁻¹) ^ n by positivity) hscale hd0.le
    have heq : (((2 : ℝ)⁻¹) ^ n) ^ d = (((2 : ℝ) ^ d) ^ n)⁻¹ := by
      rw [← Real.rpow_natCast_mul (by positivity), mul_comm (n : ℝ) d,
        Real.rpow_mul_natCast (by positivity), Real.inv_rpow (by norm_num), inv_pow]
    rw [heq, Real.mul_rpow (by norm_num) hr.le] at hscale'
    have hfactor : 1 ≤ ((2 : ℝ) ^ d * r ^ d) * ((2 : ℝ) ^ d) ^ n := by
      have hp : 0 < ((2 : ℝ) ^ d) ^ n := by positivity
      have := mul_le_mul_of_nonneg_right hscale' hp.le
      simpa [hp.ne'] using this
    let a : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ d) ^ n
    have ha0 : a ≠ 0 := by dsimp [a]; positivity
    have hat : a ≠ ∞ := by dsimp [a]; simp
    have hfactor' : 1 ≤ (ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d)) * a := by
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (((2 : ℝ) ^ d * r ^ d) * ((2 : ℝ) ^ d) ^ n) :=
          ENNReal.ofReal_le_ofReal hfactor
        _ = _ := by rw [ENNReal.ofReal_mul (mul_nonneg htwo hR), ENNReal.ofReal_mul htwo,
          ENNReal.ofReal_pow htwo]
    calc
      _ ≤ unitSingularPairNear z q (((2 : ℝ)⁻¹) ^ n) b :=
        unitSingularPairNear_mono z q b hnhi
      _ ≤ ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) / a := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).2
        simpa [a, mul_comm] using hdy n
      _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d)) *
          ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) := by
        apply (ENNReal.div_le_iff_le_mul (Or.inl ha0) (Or.inl hat)).2
        calc
          _ = 1 * ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) := by simp
          _ ≤ ((ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d)) * a) *
              ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) := by gcongr
          _ = _ := by ac_rfl
      _ ≤ _ := by
        have : ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d) *
            ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) =
            ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (unitSingularPairDyadicEnvelopeReal z q d b) *
              ENNReal.ofReal (r ^ d) := by ac_rfl
        rw [this]
        exact le_self_add
  · have hrpow : 1 ≤ r ^ d := by
      have := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) (by linarith : (1 : ℝ) ≤ r) hd0.le
      simpa using this
    have hrpow' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (r ^ d) := by
      simpa using ENNReal.ofReal_le_ofReal hrpow
    calc
      _ ≤ unitSingularPairOccupation z q b := unitSingularPairNear_le_occupation z q r b
      _ = ENNReal.ofReal (unitSingularPairOccupationReal z q b) := by
        rw [unitSingularPairOccupationReal, ENNReal.ofReal_toReal hocc.ne]
      _ ≤ ENNReal.ofReal (unitSingularPairOccupationReal z q b) * ENNReal.ofReal (r ^ d) := by
        calc
          _ = ENNReal.ofReal (unitSingularPairOccupationReal z q b) * 1 := by simp
          _ ≤ _ := by gcongr
      _ ≤ _ := le_add_self

end HarmonicBalls
