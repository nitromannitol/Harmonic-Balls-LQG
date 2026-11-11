import HarmonicBalls.Proofs.Sec11.ConditionalPositiveIntersection

/-! # Conditional positivity under outside-preserving shifts -/

namespace HarmonicBalls
open MeasureTheory Set Filter

/-- An event has positive conditional probability almost surely if it meets
    every positive-measure event in the conditioning σ-algebra. -/
theorem condExp_indicator_pos_of_measure_inter_pos
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) {H : Set Ω}
    (hH : @MeasurableSet Ω m₀ H)
    (hpos : ∀ F : Set Ω, MeasurableSet[m] F → 0 < P F → 0 < P (F ∩ H)) :
    ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  let f : Ω → ℝ := H.indicator (fun _ => 1)
  let g := P[f | m]
  let Z : Set Ω := {ω | g ω ≤ 0}
  have hZm : MeasurableSet[m] Z := measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hnonneg : 0 ≤ᵐ[P] g := condExp_nonneg (Filter.Eventually.of_forall (by
    intro ω; by_cases hω : ω ∈ H <;> simp [f, hω]))
  have hz : P Z = 0 := by
    by_contra hn
    have hp : 0 < P (Z ∩ H) := hpos Z hZm (pos_iff_ne_zero.mpr hn)
    have hf : Integrable f P := (integrable_const (1 : ℝ)).indicator hH
    have hfn : 0 ≤ᵐ[P.restrict Z] f := Filter.Eventually.of_forall (by
      intro ω; by_cases hω : ω ∈ H <;> simp [f, hω])
    have hs : Function.support f ∩ Z = Z ∩ H := by
      ext ω; simp [f, and_comm]
    have hint : 0 < ∫ ω in Z, f ω ∂P :=
      (setIntegral_pos_iff_support_of_nonneg_ae hfn hf.integrableOn).2 (by rw [hs]; exact hp)
    rw [← setIntegral_condExp hm hf hZm] at hint
    have hzero : g =ᵐ[P.restrict Z] 0 := by
      change ∀ᵐ ω ∂P.restrict Z, g ω = 0
      rw [ae_restrict_iff' (hm Z hZm)]
      filter_upwards [hnonneg] with ω hω hωZ
      exact le_antisymm hωZ hω
    have : (∫ ω in Z, g ω ∂P) = 0 := by simpa using integral_congr_ae hzero
    exact (ne_of_gt hint) this
  have hzn : ∀ᵐ ω ∂P, ω ∉ Z := ae_iff.mpr (by simpa using hz)
  filter_upwards [hzn] with ω hω
  exact lt_of_not_ge hω

/-- Conditional positivity transfers through an outside-preserving map whose
    image law dominates the original law. The map sends the target event into
    the seed event in inverse-image form. -/
theorem condExp_indicator_pos_of_outside_preserving_shift
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) {B H : Set Ω}
    (hB : @MeasurableSet Ω m₀ B) (hH : @MeasurableSet Ω m₀ H)
    (τ : Ω → Ω) (hτ : @Measurable Ω Ω m₀ m₀ τ)
    (hac : P ≪ @Measure.map Ω Ω m₀ m₀ τ P)
    (hout : ∀ F : Set Ω, MeasurableSet[m] F → ∀ᵐ ω ∂P, (ω ∈ F ↔ τ ω ∈ F))
    (hshift : ∀ᵐ ω ∂P, τ ω ∈ B → ω ∈ H)
    (hseed : ∀ᵐ ω ∂P, 0 < (P[B.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  let : MeasurableSpace Ω := m₀
  apply condExp_indicator_pos_of_measure_inter_pos P m hm hH
  intro F hF hp
  have hFB : 0 < P (F ∩ B) := measure_inter_pos_of_condExp_indicator_pos P m hm hF hB hp hseed
  have hmapped : 0 < P.map τ (F ∩ B) := by
    by_contra hn
    have hz : P.map τ (F ∩ B) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
    exact (ne_of_gt hFB) (hac hz)
  rw [Measure.map_apply hτ ((hm F hF).inter hB)] at hmapped
  apply hmapped.trans_le
  apply measure_mono_ae
  filter_upwards [hout F hF, hshift] with ω hω hs hmem
  exact ⟨hω.mpr hmem.1, hs hmem.2⟩

end HarmonicBalls
