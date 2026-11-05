import HarmonicBalls.Proofs.Sec11.SingularWeylExhaustion
import HarmonicBalls.Proofs.Sec11.ContinuousBaseMetricShiftDecoder

/-! # Common normalization for exhaustion decoders

Countable families of normalized observables can be combined into an
observable for their infimum when deterministic normalization factors are
reconciled with a common finite factor.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- Combining a countable family of normalized measurable decoders by an
infimum gives a decoder with the common normalization. The observations and
exceptional null sets may depend on the index of the family of shifts. -/
theorem exists_normalized_iInf_decoder
    {Ω X G : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    (F : ℕ → X → ℕ → ℝ≥0∞) (hF : ∀ m, Measurable (F m))
    (Y : G → Ω → X) (a : ℕ → ℝ≥0∞)
    (w : G → Ω → ℕ → ℝ≥0∞) (wref : G → Ω → ℝ≥0∞)
    (d : G → Ω → ℕ → ℕ → ℝ≥0∞)
    (hvalue : ∀ g m, ∀ᵐ ω ∂P, ∀ n, F m (Y g ω) n = w g ω m * d g ω m n)
    (hnorm : ∀ g, ∀ᵐ ω ∂P, wref g ω ≠ ∞ ∧ ∀ m, a m * w g ω m = wref g ω) :
    ∃ T : X → ℕ → ℝ≥0∞, Measurable T ∧ ∀ g, ∀ᵐ ω ∂P, ∀ n,
      T (Y g ω) n = wref g ω * ⨅ m, d g ω m n := by
  let T : X → ℕ → ℝ≥0∞ := fun v n => ⨅ m, a m * F m v n
  have hT : Measurable T := by
    apply measurable_pi_iff.mpr
    intro n
    apply Measurable.iInf
    intro m
    exact measurable_const.mul ((measurable_pi_apply n).comp (hF m))
  refine ⟨T, hT, ?_⟩
  intro g
  have hvals : ∀ᵐ ω ∂P, ∀ m n, F m (Y g ω) n = w g ω m * d g ω m n :=
    (ae_all_iff).2 (hvalue g)
  filter_upwards [hvals, hnorm g] with ω hv hn n
  change (⨅ m, a m * F m (Y g ω) n) = _
  calc
    (⨅ m, a m * F m (Y g ω) n) = ⨅ m, wref g ω * d g ω m n := by
      apply iInf_congr
      intro m
      rw [hv m n, ← mul_assoc, hn.2 m]
    _ = wref g ω * ⨅ m, d g ω m n := by
      rw [ENNReal.mul_iInf (fun ht _ => (hn.1 ht).elim)]

/-- The deterministic factor that changes the cutoff normalization from
`b` to `a` is independent of the field and of its added smooth shift. -/
theorem cutoff_normalization_factor (ξ t a b : ℝ) :
    ENNReal.ofReal (Real.exp (ξ * (b - a))) *
      ENNReal.ofReal (Real.exp (ξ * (-(t + b)))) =
      ENNReal.ofReal (Real.exp (ξ * (-(t + a)))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- Continuous shifts contribute the same test-function pairing to every
cutoff normalization, so their correction factor is deterministic. -/
theorem cutoff_normalization_factor_pairing (ξ t : ℝ) (ψ g f₀ f : ℂ → ℝ)
    (hψ : IsTestFunction Set.univ ψ) (hg : Continuous g)
    (hf₀ : Continuous f₀) (hf : Continuous f) :
    ENNReal.ofReal (Real.exp (ξ * ((∫ z, f z * ψ z) - ∫ z, f₀ z * ψ z))) *
      ENNReal.ofReal (Real.exp (ξ * (-(t + ∫ z, (g z + f z) * ψ z)))) =
      ENNReal.ofReal (Real.exp (ξ * (-(t + ∫ z, (g z + f₀ z) * ψ z)))) := by
  have hi (k : ℂ → ℝ) (hk : Continuous k) : Integrable (fun z => k z * ψ z) :=
    (hk.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hsplit (k : ℂ → ℝ) (hk : Continuous k) :
      (∫ z, (g z + k z) * ψ z) = (∫ z, g z * ψ z) + ∫ z, k z * ψ z := by
    simp_rw [add_mul]
    exact integral_add (hi g hg) (hi k hk)
  rw [hsplit f hf, hsplit f₀ hf₀, ← add_assoc, ← add_assoc]
  exact cutoff_normalization_factor ξ (t + ∫ z, g z * ψ z)
    (∫ z, f₀ z * ψ z) (∫ z, f z * ψ z)

#print axioms cutoff_normalization_factor_pairing

#print axioms cutoff_normalization_factor

#print axioms exists_normalized_iInf_decoder

end HarmonicBalls
