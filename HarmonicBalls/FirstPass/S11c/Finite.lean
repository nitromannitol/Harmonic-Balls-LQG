import HarmonicBalls.Steps.Sec11.WeylFieldZero
import HarmonicBalls.Steps.Sec11.WeylScalingOrder
import HarmonicBalls.Proofs.GFF.MetricXiSign
import HarmonicBalls.Proposed.LQG

/-!
# Finiteness of the Weyl-scaled LQG metric for weights bounded above (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic reduction). Let `D` be the LQG metric of a field with the staged Fact 2.2 I-IV
(`LQGMetricFieldAxioms`, `Proposed/LQG.lean`). Almost surely, every Weyl weight `f` bounded above has finite
Weyl-scaled distances, and its real representative satisfies the forward identity `ofReal (toReal d) = d`.
This supplies the `hscale` input of `shifted_sup_le_of_good` (`FirstPass/S11c/Shifted.lean`) for the shift
`f` of the Cameron-Martin step (a continuous compactly supported `f` is bounded above).

Proof, from repo-proved lemmas only: the zero weight is finite a.s. (`ae_weylScaling_zero_of_metricFieldAxioms`);
the weight is dominated by the constant weight `B` (`weylScaling_mono_exponent`, needs `0 ≤ ξ`); a constant
weight scales by `exp(ξ B)` (`weylScaling_add_const`). The sign `0 < ξ` is `IsLQGMetric.weylExponent_pos`.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Weyl-scaled distances of a weight bounded above are finite almost surely, and their real representatives
satisfy the forward identity. -/
theorem ae_weylScaling_bddAbove_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, (∃ B : ℝ, ∀ z, f z ≤ B) → ∀ u v,
      weylScaling (D ω) ξ f u v < ∞ ∧
      ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) = weylScaling (D ω) ξ f u v := by
  have hξ : 0 ≤ ξ := by
    obtain ⟨𝔇, h𝔇, _⟩ := hD
    exact (IsLQGMetric.weylExponent_pos h𝔇 hγ).le
  filter_upwards [ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD]
    with ω hzero
  intro f hf u v
  obtain ⟨B, hB⟩ := hf
  have hle : weylScaling (D ω) ξ f u v ≤ weylScaling (D ω) ξ (fun _ => B) u v :=
    weylScaling_mono_exponent (D ω) ξ f (fun _ => B)
      (fun z => mul_le_mul_of_nonneg_left (hB z) hξ) u v
  have hconst : weylScaling (D ω) ξ (fun _ => B) u v
      = ENNReal.ofReal (Real.exp (ξ * B)) * weylScaling (D ω) ξ 0 u v := by
    have h := weylScaling_add_const (D ω) ξ B (0 : ℂ → ℝ) u v
    simp only [Pi.zero_apply, zero_add] at h
    exact h
  have hfin : weylScaling (D ω) ξ f u v < ∞ := by
    refine lt_of_le_of_lt hle ?_
    rw [hconst, hzero u v]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  exact ⟨hfin, ENNReal.ofReal_toReal hfin.ne⟩

end HarmonicBalls
