import HarmonicBalls.Proofs.Sec11.ConditionalDyadicFullSupport
import HarmonicBalls.Proofs.Sec11.PinchSecondConditionalAssemblyNull

/-! # Conditional mass and diameter under core containment -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped ENNReal

/-- Passing from a set to its closure does not decrease its internal diameter. -/
theorem internalDiam_le_closure (D : ℂ → ℂ → ℝ) (δ : ℝ) (V : Set ℂ) :
    internalDiam D δ V ≤ internalDiam D δ (closure V) := by
  unfold internalDiam
  rw [thickening_closure]
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup_of_le x (le_iSup_of_le (subset_closure hx)
    (le_iSup_of_le y (le_iSup_of_le (subset_closure hy) le_rfl)))

/-- Conditional positivity passes from a null-measurable event to a
null-measurable event containing it. -/
theorem condExp_indicator_pos_of_subset_null
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) {S T : Set Ω}
    (hS : @NullMeasurableSet Ω m₀ S P) (hT : @NullMeasurableSet Ω m₀ T P) (hST : S ⊆ T)
    (hpos : ∀ᵐ ω ∂P, 0 < (P[S.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    ∀ᵐ ω ∂P, 0 < (P[T.indicator (fun _ => (1 : ℝ)) | m]) ω := by
  let : MeasurableSpace Ω := m₀
  have hSi : Integrable (S.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).integrableOn.integrable_indicator₀ hS
  have hTi : Integrable (T.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).integrableOn.integrable_indicator₀ hT
  have hle : S.indicator (fun _ => (1 : ℝ)) ≤ᵐ[P] T.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards with ω
    by_cases hs : ω ∈ S
    · have ht := hST hs
      simp [hs, ht]
    · by_cases ht : ω ∈ T <;> simp [hs, ht]
  filter_upwards [hpos, condExp_mono (m := m) hSi hTi hle] with ω hp hm
  exact hp.trans_le hm

/-- A mass certificate on a square inside `U`, together with a diameter
certificate on the closure of `V`, supplies the target certificate. -/
theorem condExp_mass_diameter_pos_of_square_closure
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (S U V : Set ℂ) (δ : ℝ) (c d : ℝ≥0∞) (hSU : S ⊆ U)
    (hS : @NullMeasurableSet Ω m₀
      {ω | c < μ ω S ∧ internalDiam (D ω) δ (closure V) < d} P)
    (hT : @NullMeasurableSet Ω m₀
      {ω | internalDiam (D ω) δ V < d ∧ c < μ ω U} P)
    (hpos : ∀ᵐ ω ∂P, 0 < (P[({ω | c < μ ω S ∧
      internalDiam (D ω) δ (closure V) < d}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (D ω) δ V < d ∧
      c < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω := by
  apply condExp_indicator_pos_of_subset_null P m hS hT ?_ hpos
  intro ω hω
  exact ⟨(internalDiam_le_closure (D ω) δ V).trans_lt hω.2,
    hω.1.trans_le (measure_mono hSU)⟩

end HarmonicBalls
