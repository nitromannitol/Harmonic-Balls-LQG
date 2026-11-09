import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# First pass, conditional positivity (fp-S11e2, owner n2)

General probability fact used in the event `E₂` of Lemma 11.17 (paper `lemma:E2`, lines 3697-3725): if the conditional
probability of `H` given a sub-σ-algebra `m` is almost surely positive, and `F` is `m`-measurable with positive
probability, then `P (F ∩ H) > 0`. The proof is `P (F ∩ H) = ∫_F P[1_H | m] dP` (`setIntegral_condExp`), a set integral
of an almost surely positive function over a set of positive measure. This is classical measure theory (EXTERNAL), no
hypothesis about the LQG field.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

/-- `P (F ∩ H) > 0` when `P[1_H | m] > 0` almost surely and `F ∈ m` has positive probability. -/
theorem measure_inter_pos_of_condExp_indicator_pos {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (P : Measure Ω) [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {F H : Set Ω} (hF : MeasurableSet[m] F) (hH : MeasurableSet[m₀] H) (hFpos : 0 < P F)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) | m]) ω) :
    0 < P (F ∩ H) := by
  have hint : Integrable (H.indicator (1 : Ω → ℝ)) P := (integrable_const (1 : ℝ)).indicator hH
  have hF₀ : MeasurableSet[m₀] F := hm _ hF
  have hnonneg : 0 ≤ᵐ[P] (P[H.indicator (1 : Ω → ℝ) | m]) :=
    condExp_nonneg (Eventually.of_forall fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hsupp : ∀ᵐ ω ∂P, ω ∈ Function.support (P[H.indicator (1 : Ω → ℝ) | m]) :=
    hcond.mono fun ω h => (Function.mem_support.mpr h.ne')
  have heq : F ∩ Function.support (P[H.indicator (1 : Ω → ℝ) | m]) =ᵐ[P] F := by
    filter_upwards [hsupp] with ω hω
    simp [hω]
  have hPF : P (F ∩ Function.support (P[H.indicator (1 : Ω → ℝ) | m])) = P F := measure_congr heq
  have hpos : 0 < ∫ ω in F, (P[H.indicator (1 : Ω → ℝ) | m]) ω ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_ae hnonneg) integrable_condExp.integrableOn, Set.inter_comm]
    rw [hPF]
    exact hFpos
  have hsame : ∫ ω in F, (P[H.indicator (1 : Ω → ℝ) | m]) ω ∂P = ∫ ω in F, H.indicator (1 : Ω → ℝ) ω ∂P :=
    setIntegral_condExp hm hint hF
  rw [hsame, ← integral_indicator hF₀, Set.indicator_indicator, integral_indicator_one (hF₀.inter hH),
    measureReal_def] at hpos
  exact (ENNReal.toReal_pos_iff.mp hpos).1

#print axioms measure_inter_pos_of_condExp_indicator_pos

end HarmonicBalls
