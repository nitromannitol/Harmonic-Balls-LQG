import HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift
import HarmonicBalls.Proofs.Sec11.RandomConstantPairingLaw

/-! # Smooth shifts of singular fields modulo constants

The Cameron–Martin theorem used here is Leonardo Bonanno's LatticeProb
formalization. The comparison concerns the joint process of all local
zero-integral test pairings, including the same logarithmic insertion on
both sides.
-/

noncomputable section

open MeasureTheory Set

namespace HarmonicBalls

/-- A smooth compactly supported shift preserves the law class of the local
log-singular field modulo constants. -/
theorem IsWholePlaneGFF.singular_smooth_shift_modConst_pairing_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) :
    P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) ≪
        P.map (localModConstPairings α hC U) ∧
      P.map (localModConstPairings α hC U) ≪
        P.map (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) := by
  let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
  let Y : Ω → RawMeanZeroTest → ℝ :=
    fun ω φ => hC ω φ.1 + ∫ x, φ.1 x * g x
  let R : (RawMeanZeroTest → ℝ) → LocalZeroMeanTest U → ℝ := fun v φ =>
    v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ -
      α * ∫ x, φ.1 x * Real.log ‖x‖
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hh.measurable_pairing φ.1 φ.2.1
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    (hh.measurable_pairing φ.1 φ.2.1).add_const _
  have hR : Measurable R := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply
      (⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩ : RawMeanZeroTest)).sub_const _
  have hRX : R ∘ X = localModConstPairings α hC U := rfl
  have hRY : R ∘ Y = localModConstPairings α (fun ω => addFunPairing (hC ω) g) U := by
    funext ω φ
    simp only [Function.comp_apply, R, Y, localModConstPairings, fieldPairing, addFunPairing]
    congr 2
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have h := hh.smooth_shift_raw_pairing_laws hg
  change P.map Y ≪ P.map X ∧ P.map X ≪ P.map Y at h
  have hf := h.1.map hR
  have hb := h.2.map hR
  rw [Measure.map_map hR hY, Measure.map_map hR hX, hRY, hRX] at hf hb
  exact ⟨hf, hb⟩

/-- The shifted local law remains dominated after an absolutely continuous
change of sample law and arbitrary random choices of additive constant. -/
theorem IsWholePlaneGFF.singular_smooth_shift_modConst_law_of_dominated
    {Ω : Type*} [MeasurableSpace Ω] {P Q : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF Q hC hcirc) (hPQ : P ≪ Q)
    {g : ℂ → ℝ} (hg : IsTestFunction univ g) (α : ℝ) (U : Set ℂ)
    (c d : Ω → ℝ) :
    P.map (localModConstPairings α (fun ω =>
      addFunPairing (addFunPairing (hC ω) g) (fun _ => c ω)) U) ≪
    Q.map (localModConstPairings α (fun ω =>
      addFunPairing (hC ω) (fun _ => d ω)) U) := by
  rw [localModConstPairings_add_random_constant, localModConstPairings_add_random_constant]
  have hm : Measurable (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U) := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).add_const _).sub_const _
  exact (hPQ.map hm).trans (hh.singular_smooth_shift_modConst_pairing_laws hg α U).1

#print axioms IsWholePlaneGFF.singular_smooth_shift_modConst_pairing_laws
#print axioms IsWholePlaneGFF.singular_smooth_shift_modConst_law_of_dominated

end HarmonicBalls
