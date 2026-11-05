import HarmonicBalls.Proofs.Sec11.SingularSmoothShiftPairing
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! # Smooth shifts on the canonical local pairing space

A smooth shift acts directly on the local field modulo constants. Its forward
and inverse maps are quasi-measure-preserving for the singular-field pairing
law. The Cameron–Martin input is Leonardo Bonanno's LatticeProb formalization.
No reconstruction of the metric or circle averages is asserted here.
-/

noncomputable section

open MeasureTheory Set

namespace HarmonicBalls

/-- Translation of all local zero-integral field pairings by a deterministic
smooth function. -/
def localModConstPairingShift (U : Set ℂ) (g : ℂ → ℝ)
    (v : LocalZeroMeanTest U → ℝ) : LocalZeroMeanTest U → ℝ :=
  fun φ => v φ + ∫ x, g x * φ.1 x

/-- The inverse translation on the local zero-integral pairing space. -/
def localModConstPairingUnshift (U : Set ℂ) (g : ℂ → ℝ)
    (v : LocalZeroMeanTest U → ℝ) : LocalZeroMeanTest U → ℝ :=
  fun φ => v φ - ∫ x, g x * φ.1 x

/-- The two translations are inverse measurable maps. -/
theorem localModConstPairingShift_measurableEquiv (U : Set ℂ) (g : ℂ → ℝ) :
    Function.LeftInverse (localModConstPairingUnshift U g) (localModConstPairingShift U g) ∧
    Function.RightInverse (localModConstPairingUnshift U g) (localModConstPairingShift U g) ∧
    Measurable (localModConstPairingShift U g) ∧
    Measurable (localModConstPairingUnshift U g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    funext φ
    simp only [localModConstPairingUnshift, localModConstPairingShift, add_sub_cancel_right]
  · intro v
    funext φ
    simp only [localModConstPairingUnshift, localModConstPairingShift, sub_add_cancel]
  · exact measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).add_const _
  · exact measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).sub_const _

/-- For the local singular-field law, canonical smooth translation and its
inverse are quasi-measure-preserving, and translation implements addition of
the smooth function in every pairing. -/
theorem IsWholePlaneGFF.quasiMeasurePreserving_localModConstPairingShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) :
    let Q := P.map (localModConstPairings α hC U)
    Measure.QuasiMeasurePreserving (localModConstPairingShift U g) Q Q ∧
    Measure.QuasiMeasurePreserving (localModConstPairingUnshift U g) Q Q ∧
    (∀ ω, localModConstPairingShift U g (localModConstPairings α hC U ω) =
      localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) := by
  let A := localModConstPairings α hC U
  let B := localModConstPairings α (fun ω => addFunPairing (hC ω) g) U
  let S := localModConstPairingShift U g
  let T := localModConstPairingUnshift U g
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  have heq : S ∘ A = B := by
    funext ω φ
    simp only [Function.comp_apply, S, A, B, localModConstPairingShift,
      localModConstPairings, fieldPairing, addFunPairing]
    ring
  obtain ⟨hinv, _, hS, hT⟩ := localModConstPairingShift_measurableEquiv U g
  have hmaps : (P.map A).map S = P.map B := by rw [Measure.map_map hS hA, heq]
  have hdom := hh.singular_smooth_shift_modConst_pairing_laws hg α U
  change P.map B ≪ P.map A ∧ P.map A ≪ P.map B at hdom
  refine ⟨⟨hS, ?_⟩, ⟨hT, ?_⟩, ?_⟩
  · rw [hmaps]
    exact hdom.1
  · have h := hdom.2.map hT
    rw [← hmaps, Measure.map_map hT hS] at h
    have hcomp : T ∘ S = id := funext hinv
    change (P.map A).map T ≪ (P.map A).map (T ∘ S) at h
    rw [hcomp, Measure.map_id] at h
    exact h
  · intro ω
    exact congrFun heq ω

/-- Any event on the canonical local pairing space has positive mass exactly
when its smooth-shift preimage does. No event measurability is required. -/
theorem IsWholePlaneGFF.localModConstPairingShift_preimage_pos_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) (A : Set (LocalZeroMeanTest U → ℝ)) :
    let Q := P.map (localModConstPairings α hC U)
    0 < Q ((localModConstPairingShift U g) ⁻¹' A) ↔ 0 < Q A := by
  obtain ⟨hS, hT, _⟩ := hh.quasiMeasurePreserving_localModConstPairingShift hg α U
  obtain ⟨_, hinv, _, _⟩ := localModConstPairingShift_measurableEquiv U g
  constructor
  · intro hpos
    by_contra hn
    have hz : P.map (localModConstPairings α hC U) A = 0 :=
      le_antisymm (le_of_not_gt hn) (zero_le)
    exact (ne_of_gt hpos) (hS.preimage_null hz)
  · intro hpos
    by_contra hn
    have hz : P.map (localModConstPairings α hC U)
        ((localModConstPairingShift U g) ⁻¹' A) = 0 :=
      le_antisymm (le_of_not_gt hn) (zero_le)
    have hz' := hT.preimage_null hz
    have heq : (localModConstPairingUnshift U g) ⁻¹'
        ((localModConstPairingShift U g) ⁻¹' A) = A := by
      ext v
      change localModConstPairingShift U g (localModConstPairingUnshift U g v) ∈ A ↔ v ∈ A
      rw [hinv v]
    rw [heq] at hz'
    exact (ne_of_gt hpos) hz'

/-- Any measurable observation decoded from the canonical local pairing
space has equivalent laws before and after a smooth shift. This applies to
arbitrary measurable target spaces. -/
theorem IsWholePlaneGFF.localModConstPairingShift_observable_laws
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g)
    (α : ℝ) (U : Set ℂ) (F : (LocalZeroMeanTest U → ℝ) → E) (hF : Measurable F) :
    let Q := P.map (localModConstPairings α hC U)
    Q.map (F ∘ localModConstPairingShift U g) ≪ Q.map F ∧
      Q.map F ≪ Q.map (F ∘ localModConstPairingShift U g) := by
  let A := localModConstPairings α hC U
  let B := localModConstPairings α (fun ω => addFunPairing (hC ω) g) U
  let S := localModConstPairingShift U g
  have hA : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - α * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  obtain ⟨_, _, hS, _⟩ := localModConstPairingShift_measurableEquiv U g
  have heq : S ∘ A = B := by
    funext ω
    exact (hh.quasiMeasurePreserving_localModConstPairingShift hg α U).2.2 ω
  have hmaps : (P.map A).map S = P.map B := by rw [Measure.map_map hS hA, heq]
  have h := hh.singular_smooth_shift_modConst_pairing_laws hg α U
  change P.map B ≪ P.map A ∧ P.map A ≪ P.map B at h
  rw [← hmaps] at h
  have hf := h.1.map hF
  have hb := h.2.map hF
  rw [Measure.map_map hF hS] at hf hb
  exact ⟨hf, hb⟩

#print axioms IsWholePlaneGFF.localModConstPairingShift_observable_laws
#print axioms IsWholePlaneGFF.localModConstPairingShift_preimage_pos_iff
#print axioms localModConstPairingShift_measurableEquiv
#print axioms IsWholePlaneGFF.quasiMeasurePreserving_localModConstPairingShift

end HarmonicBalls
