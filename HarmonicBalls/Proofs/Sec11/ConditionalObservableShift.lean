import HarmonicBalls.Proofs.Sec11.ConditionalPositivityShift
import HarmonicBalls.Proofs.Sec11.SingularSmoothShiftPairing

/-! # Conditional positivity from shifted field observables

The Cameron–Martin input is Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Filter

/-- An interior shift may be represented at the level of field observables:
if it preserves the outside observation and its law is dominated by the
original observable law, positivity after a suitable shift on every outside
event implies conditional positivity of the original event. The shift may
depend on the outside event. -/
theorem condExp_indicator_pos_of_shifted_observables
    {Ω E O : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace O]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) (W : E → O) (hW : Measurable W)
    (B : Set E) (hB : MeasurableSet B)
    (hpos : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (W ∘ X) inferInstance] F → 0 < P F →
      ∃ Y : Ω → E, Measurable Y ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, W (Y ω) = W (X ω)) ∧
        0 < P {ω | ω ∈ F ∧ Y ω ∈ B}) :
    ∀ᵐ ω ∂P, 0 < (P[(X ⁻¹' B).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (W ∘ X) inferInstance]) ω := by
  have hm : MeasurableSpace.comap (W ∘ X) inferInstance ≤ mΩ :=
    measurable_iff_comap_le.mp (hW.comp hX)
  apply condExp_indicator_pos_of_measure_inter_pos P _ hm (hX hB)
  intro F hF hFp
  obtain ⟨Y, hY, hac, hpreserve, hp⟩ := hpos F hF hFp
  obtain ⟨C, hC, hFC⟩ := MeasurableSpace.measurableSet_comap.mp hF
  rw [← hFC] at hp ⊢
  have heq : {ω | ω ∈ (W ∘ X) ⁻¹' C ∧ Y ω ∈ B} =ᵐ[P] Y ⁻¹' (W ⁻¹' C ∩ B) := by
    filter_upwards [hpreserve] with ω hω
    simp only [mem_preimage, Function.comp_apply, mem_inter_iff, hω]
  have hpY : 0 < P.map Y (W ⁻¹' C ∩ B) := by
    rw [Measure.map_apply hY ((hW hC).inter hB)]
    rwa [← measure_congr heq]
  have hpX : 0 < P.map X (W ⁻¹' C ∩ B) := by
    by_contra h
    exact (ne_of_gt hpY) (hac (nonpos_iff_eq_zero.mp (not_lt.mp h)))
  rw [Measure.map_apply hX ((hW hC).inter hB)] at hpX
  simpa only [preimage_inter, preimage_comp] using hpX

#print axioms condExp_indicator_pos_of_shifted_observables

/-- Smooth shifts supported away from the outside observation can be chosen
separately for each outside event when establishing conditional positivity. -/
theorem IsWholePlaneGFF.condExp_modConst_pos_of_interior_shifts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ) (U : Set ℂ)
    (B : Set (LocalZeroMeanTest univ → ℝ)) (hB : MeasurableSet B)
    (hpos : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings α hC U) inferInstance] F →
      0 < P F → ∃ g : ℂ → ℝ, IsTestFunction univ g ∧
        (∀ z ∈ U, g z = 0) ∧
        0 < P {ω | ω ∈ F ∧ localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) univ ω ∈ B}) :
    ∀ᵐ ω ∂P, 0 < (P[((localModConstPairings α hC univ) ⁻¹' B).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap
        (localModConstPairings α hC U) inferInstance]) ω := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X := localModConstPairings α hC univ
  let W : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest U → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hW : Measurable W := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    (hh.measurable_pairing φ.1 φ.2.1).sub_const _
  have hWX : W ∘ X = localModConstPairings α hC U := rfl
  rw [← hWX]
  apply condExp_indicator_pos_of_shifted_observables P X hX W hW B hB
  intro F hF hFp
  rw [hWX] at hF
  obtain ⟨g, hg, hgU, hp⟩ := hpos F hF hFp
  let Y := localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    ((hh.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  refine ⟨Y, hY, (hh.singular_smooth_shift_modConst_pairing_laws hg α univ).1, ?_, hp⟩
  filter_upwards [] with ω
  funext φ
  have hzero : (fun z => g z * φ.1 z) = 0 := by
    funext z
    by_cases hz : z ∈ U
    · simp [hgU z hz]
    · have hφ : φ.1 z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz' => hz (φ.2.1.2.2 hz'))
      simp [hφ]
  simp [W, X, Y, localModConstPairings, fieldPairing, addFunPairing, hzero]

#print axioms IsWholePlaneGFF.condExp_modConst_pos_of_interior_shifts
end HarmonicBalls
