import HarmonicBalls.Proofs.Sec11.SingularSmoothShiftPairing

/-! # Smooth shifts of modulo-constant field observables

The Cameron–Martin input is Leonardo Bonanno's LatticeProb formalization.
The induced observable under a shift is defined through a common field
decoder; identifying it with a particular metric or measure is separate.
-/

noncomputable section

open MeasureTheory Set Filter

namespace HarmonicBalls

/-- A standard Borel observable of the local field modulo constants has a
measurable field decoder whose shifted and unshifted laws are equivalent. -/
theorem IsWholePlaneGFF.exists_smooth_shift_modConst_observable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) (X : Ω → E)
    (hX : Measurable[Section6.fieldSigmaAlgebraModConst α hC U] X) :
    ∃ F : (LocalZeroMeanTest U → ℝ) → E, Measurable F ∧
      (∀ ω, F (localModConstPairings α hC U ω) = X ω) ∧
      Measurable (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) ∧
      P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) ≪
        P.map X ∧
      P.map X ≪
        P.map (F ∘ localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) := by
  let A := localModConstPairings α hC U
  let B := localModConstPairings α (fun ω => addFunPairing (hC ω) g) U
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hB : Measurable B := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hX' : Measurable[MeasurableSpace.comap A inferInstance] X := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact hX
  obtain ⟨F, hF, heq⟩ := hX'.exists_eq_measurable_comp
  have h := hh.singular_smooth_shift_modConst_pairing_laws hg α U
  change P.map B ≪ P.map A ∧ P.map A ≪ P.map B at h
  have hf := h.1.map hF
  have hb := h.2.map hF
  rw [Measure.map_map hF hB, Measure.map_map hF hA, ← heq] at hf hb
  exact ⟨F, hF, fun ω => (congrFun heq ω).symm, hF.comp hB, hf, hb⟩

/-- Two measurable decoders that agree almost surely for the original field
also agree almost surely after a smooth compactly supported shift. -/
theorem IsWholePlaneGFF.ae_eq_modConst_decoders_after_smooth_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) (F G : (LocalZeroMeanTest U → ℝ) → E)
    (hF : Measurable F) (hG : Measurable G)
    (hEq : ∀ᵐ ω ∂P, F (localModConstPairings α hC U ω) =
      G (localModConstPairings α hC U ω)) :
    ∀ᵐ ω ∂P,
      F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) =
      G (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) := by
  let A := localModConstPairings α hC U
  let B := localModConstPairings α (fun ω => addFunPairing (hC ω) g) U
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have hB : Measurable B := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  have hs : MeasurableSet {v | F v = G v} := measurableSet_eq_fun hF hG
  have hbase : ∀ᵐ v ∂P.map A, F v = G v := (ae_map_iff hA.aemeasurable hs).2 hEq
  have hac := (hh.singular_smooth_shift_modConst_pairing_laws hg α U).1
  exact (ae_map_iff hB.aemeasurable hs).1 (hac.ae_le hbase)

#print axioms IsWholePlaneGFF.exists_smooth_shift_modConst_observable
#print axioms IsWholePlaneGFF.ae_eq_modConst_decoders_after_smooth_shift

end HarmonicBalls
