import HarmonicBalls.Proofs.Sec11.ConditionalPositiveIntersection

/-! # Conditional positivity for almost everywhere measurable events -/

namespace HarmonicBalls
open MeasureTheory Set Filter

/-- Conditional positivity also gives a positive intersection when the
inside event is measurable after completion of the probability space. -/
theorem measure_inter_pos_of_condExp_indicator_pos_nullMeasurable
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) {F H : Set Ω}
    (hF : MeasurableSet[m] F) (hH : @NullMeasurableSet Ω m₀ H P) (hFp : 0 < P F)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P (F ∩ H) := by
  let : MeasurableSpace Ω := m₀
  obtain ⟨H', _, hH', heq⟩ := hH.exists_measurable_subset_ae_eq
  have hi : H'.indicator (fun _ => (1 : ℝ)) =ᵐ[P] H.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [heq] with ω hω
    by_cases hh : ω ∈ H' <;> simp_all
  have hc : ∀ᵐ ω ∂P, 0 < (P[H'.indicator (fun _ => (1 : ℝ)) | m]) ω := by
    filter_upwards [hcond, condExp_congr_ae (m := m) hi] with ω hp he
    rw [he]
    exact hp
  have hp := measure_inter_pos_of_condExp_indicator_pos P m hm hF hH' hFp hc
  have hinter : F ∩ H' =ᵐ[P] F ∩ H := by
    filter_upwards [heq] with ω hω
    simp only [mem_inter_iff]
    exact propext (and_congr_right fun _ => iff_of_eq hω)
  rwa [measure_congr hinter] at hp

#print axioms measure_inter_pos_of_condExp_indicator_pos_nullMeasurable
end HarmonicBalls
