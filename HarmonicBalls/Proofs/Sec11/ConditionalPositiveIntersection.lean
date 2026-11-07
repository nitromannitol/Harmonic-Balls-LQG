import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Positive intersection from conditional positivity

The outside-field event in the second pinch step has positive probability,
while the inside-field event has positive conditional probability almost
surely. This lemma gives their positive-probability intersection. -/

open MeasureTheory Set Filter

namespace HarmonicBalls

/-- An event of positive probability measurable for a sub-σ-algebra has
positive intersection with an event whose conditional probability is
almost surely positive. -/
theorem measure_inter_pos_of_condExp_indicator_pos
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) {F H : Set Ω}
    (hF : MeasurableSet[m] F) (hH : @MeasurableSet Ω m₀ H) (hFp : 0 < P F)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P (F ∩ H) := by
  let f : Ω → ℝ := H.indicator (fun _ => 1)
  have hf : Integrable f P := (integrable_const (1 : ℝ)).indicator hH
  have hnonneg : 0 ≤ᵐ[P.restrict F] P[f | m] :=
    ae_mono Measure.restrict_le_self (hcond.mono fun _ hp => hp.le)
  have heq : Function.support (P[f | m]) ∩ F =ᵐ[P] F := by
    filter_upwards [hcond] with ω hω
    simp only [mem_inter_iff, Function.mem_support]
    exact propext ⟨fun h => h.2, fun h => ⟨ne_of_gt hω, h⟩⟩
  have hp : 0 < ∫ ω in F, (P[f | m]) ω ∂P :=
    (setIntegral_pos_iff_support_of_nonneg_ae hnonneg integrable_condExp.integrableOn).2 (by
      rw [measure_congr heq]
      exact hFp)
  rw [setIntegral_condExp hm hf hF] at hp
  by_contra hn
  have hz : P (F ∩ H) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
  have hzero : f =ᵐ[P.restrict F] 0 := by
    change ∀ᵐ ω ∂P.restrict F, f ω = 0
    rw [ae_restrict_iff' (hm F hF)]
    have hnull : ∀ᵐ ω ∂P, ω ∉ F ∩ H := by
      apply ae_iff.mpr
      simpa only [not_not, ofPred_mem_eq] using hz
    filter_upwards [hnull] with ω hω hωF
    have hωH : ω ∉ H := fun hh => hω ⟨hωF, hh⟩
    simp [f, hωH]
  have : (∫ ω in F, f ω ∂P) = 0 := by
    simpa using integral_congr_ae hzero
  linarith

#print axioms measure_inter_pos_of_condExp_indicator_pos
end HarmonicBalls
