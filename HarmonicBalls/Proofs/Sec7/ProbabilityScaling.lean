import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Polynomially high probability under power rescaling

The scale of the Harnack annuli is a positive power of the mass parameter in
Proposition 7.1.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- A positive power reparametrization preserves polynomially high probability. -/
theorem PolyHighProb.comp_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : PolyHighProb P E) {a : ℝ} (ha : 0 < a) :
    PolyHighProb P fun r => E (r ^ a) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨a * p, mul_pos ha hp, C, r₀ ^ a⁻¹, Real.rpow_pos_of_pos hr₀ _, ?_⟩
  intro r hr hrr
  have hlt : r ^ a < r₀ := by
    calc
      r ^ a < (r₀ ^ a⁻¹) ^ a := Real.rpow_lt_rpow hr.le hrr ha
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]
  calc
    P (E (r ^ a))ᶜ ≤ ENNReal.ofReal (C * (r ^ a) ^ p) := hE _ (Real.rpow_pos_of_pos hr _) hlt
    _ = ENNReal.ofReal (C * r ^ (a * p)) := by rw [Real.rpow_mul hr.le]

end HarmonicBalls
