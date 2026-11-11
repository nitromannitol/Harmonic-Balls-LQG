import HarmonicBalls.Steps.Sec11.SingularFieldWeylForward

/-!
# Section 11: finiteness of a Weyl weight bounded above

The singular-field finiteness lemma `ae_singularField_negative_weylScaling_finite`
(`Steps/Sec11/SingularFieldWeylForward.lean:44`) covers nonpositive weights only. The positive shift `u₁ ≥ 0` of
Lemma 11.15 (corrected paper lines 3659-3696: the root and `Q` bumps multiply lengths by at most `b`) needs the same
finiteness for weights bounded above. A weight `f ≤ M` with `ξ ≥ 0` gives
`weylScaling D ξ f ≤ exp(ξ M) · weylScaling D ξ 0` (deterministic), and `weylScaling D ξ 0 = D` almost surely by the
zero identity `ae_weylScaling_zero_of_metricFieldAxioms`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Deterministic upper comparison of Weyl scalings: for `ξ ≥ 0` and a weight `f ≤ M`,
`weylScaling D ξ f ≤ exp(ξ M) · weylScaling D ξ 0` pointwise. -/
theorem weylScaling_le_exp_mul_zero_of_le (D : ℂ → ℂ → ℝ) {ξ M : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ)
    (hf : ∀ z, f z ≤ M) (u v : ℂ) :
    weylScaling D ξ f u v ≤ ENNReal.ofReal (Real.exp (ξ * M)) * weylScaling D ξ 0 u v := by
  have hmono : weylScaling D ξ f u v ≤ weylScaling D ξ (fun z => (0 : ℝ) + M) u v := by
    apply weylScaling_mono_exponent
    intro z
    simpa using mul_le_mul_of_nonneg_left (hf z) hξ
  have hadd : weylScaling D ξ (fun z => (0 : ℝ) + M) u v =
      ENNReal.ofReal (Real.exp (ξ * M)) * weylScaling D ξ 0 u v :=
    weylScaling_add_const D ξ M (fun _ => 0) u v
  exact hmono.trans hadd.le

/-- Almost surely, every weight bounded above gives a finite Weyl scaling of the singular field's metric, and the
`ENNReal` value is the `ofReal` of its real part. Positive counterpart of
`ae_singularField_negative_weylScaling_finite`, with `f ≤ M` in place of `f ≤ 0`. -/
theorem ae_singularField_bounded_weylScaling_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, ∀ M : ℝ, (∀ z, f z ≤ M) → ∀ u v,
      weylScaling (D ω) ξ f u v < ∞ ∧
      ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) = weylScaling (D ω) ξ f u v := by
  filter_upwards [ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD]
    with ω hzero
  intro f M hM u v
  have hle := weylScaling_le_exp_mul_zero_of_le (D ω) hξ f hM u v
  rw [hzero u v] at hle
  have hfinite : weylScaling (D ω) ξ f u v < ∞ :=
    lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  exact ⟨hfinite, ENNReal.ofReal_toReal hfinite.ne⟩

end HarmonicBalls
