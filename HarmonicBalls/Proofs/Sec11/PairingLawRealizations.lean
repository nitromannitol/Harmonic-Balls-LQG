import HarmonicBalls.Steps.Sec11.GaussianProcessLaw
import HarmonicBalls.Proofs.Sec11.ShiftedPairingLaw

/-! # Local pairing laws across realizations

The comparison is on the full joint law of all local test pairings. The
Section 8 germ proof uses Leonardo Bonanno's LatticeProb formalization.
-/

namespace HarmonicBalls

open MeasureTheory

/-- Adding the same deterministic pairing values and changing the charge on
both realizations preserves absolute continuity of their full local joint
pairing laws. The realizations may have different sample spaces. -/
theorem localFieldPairings_map_ac_iff_of_common_shift
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω')
    (α β : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hC' : Ω' → (ℂ → ℝ) → ℝ)
    (d : (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (hP : Measurable (localFieldPairings α hC U))
    (hQ : Measurable (localFieldPairings α hC' U)) :
    P.map (localFieldPairings β (fun ω φ => hC ω φ + d φ) U) ≪
      Q.map (localFieldPairings β (fun ω φ => hC' ω φ + d φ) U) ↔
    P.map (localFieldPairings α hC U) ≪ Q.map (localFieldPairings α hC' U) := by
  let k : LocalFieldTest U → ℝ := fun φ =>
    d φ.1 + (α - β) * ∫ x, φ.1 x * Real.log ‖x‖
  let e : (LocalFieldTest U → ℝ) ≃ᵐ (LocalFieldTest U → ℝ) :=
    { toEquiv := Equiv.addRight k
      measurable_toFun := by
        apply measurable_pi_iff.mpr
        intro φ
        change Measurable (fun x : LocalFieldTest U → ℝ => x φ + k φ)
        have hm : Measurable (fun x : LocalFieldTest U → ℝ => x φ) := measurable_pi_apply φ
        exact hm.add_const (k φ)
      measurable_invFun := by
        apply measurable_pi_iff.mpr
        intro φ
        change Measurable (fun x : LocalFieldTest U → ℝ => x φ + -k φ)
        have hm : Measurable (fun x : LocalFieldTest U → ℝ => x φ) := measurable_pi_apply φ
        exact hm.add_const (-k φ) }
  have hp : localFieldPairings β (fun ω φ => hC ω φ + d φ) U =
      e ∘ localFieldPairings α hC U := by
    funext ω φ
    change _ + _ - β * _ = (_ - α * _) + (_ + (α - β) * _)
    ring
  have hq : localFieldPairings β (fun ω φ => hC' ω φ + d φ) U =
      e ∘ localFieldPairings α hC' U := by
    funext ω φ
    change _ + _ - β * _ = (_ - α * _) + (_ + (α - β) * _)
    ring
  rw [hp, hq, ← Measure.map_map e.measurable hP, ← Measure.map_map e.measurable hQ]
  constructor
  · intro h
    have h' := h.map e.symm.measurable
    simpa only [MeasurableEquiv.map_symm_map] using h'
  · intro h
    exact h.map e.measurable

/-- If a law is dominated by a whole-plane GFF law, its full local pairing
law after a deterministic shift is dominated by the shifted pairing law of
any whole-plane GFF realization. -/
theorem localFieldPairings_shifted_ac_of_dominated_gff
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P S : Measure Ω) (Q : Measure Ω')
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hS : IsWholePlaneGFF S hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc')
    (hPS : P ≪ S) (α β : ℝ) (d : (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    P.map (localFieldPairings β (fun ω φ => hC ω φ + d φ) U) ≪
      Q.map (localFieldPairings β (fun ω φ => hC' ω φ + d φ) U) := by
  have hp : Measurable (localFieldPairings α hC U) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hS.fieldSigmaAlgebra_le α U
  have hq : Measurable (localFieldPairings α hC' U) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hQ.fieldSigmaAlgebra_le α U
  apply (localFieldPairings_map_ac_iff_of_common_shift P Q α β hC hC' d U hp hq).mpr
  rw [← wholePlaneGFF_localFieldPairings_map_eq hS hQ α U]
  exact hPS.map hp

#print axioms localFieldPairings_map_ac_iff_of_common_shift
#print axioms localFieldPairings_shifted_ac_of_dominated_gff

end HarmonicBalls
