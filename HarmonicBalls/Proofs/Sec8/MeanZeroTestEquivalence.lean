import HarmonicBalls.Proofs.Sec8.WholePlaneRootInsertion

/-! # Equivalent mean-zero test-function conventions

The raw smooth compactly supported tests used in the candidate rooted-field
formula and the bundled tests used by the Section 8 pairing process carry the
same information. This file proves the deterministic reindexing and its
measurability; it assumes no rooted-field change-of-measure formula. The
imported Section 6 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Smooth compactly supported functions of integral zero, in the unbundled
convention used by the candidate whole-plane rooted-law statement. -/
def RawMeanZeroTest := {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ z, φ z = 0}

/-- The raw and bundled test-function conventions are equivalent. -/
noncomputable def meanZeroTestEquiv : LQGMetric.TestC0 ≃ RawMeanZeroTest where
  toFun φ := ⟨φ.1, Section6.isTestFunction_of_testC φ.1, φ.2⟩
  invFun φ := ⟨⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩
  left_inv φ := by
    apply Subtype.ext
    apply TestFunction.ext
    intro x
    rfl
  right_inv φ := by
    apply Subtype.ext
    rfl

/-- Reindexing a field by the equivalent test convention is measurable in
both directions for the cylinder sigma-algebras. -/
noncomputable def meanZeroFieldEquiv : (RawMeanZeroTest → ℝ) ≃ᵐ (LQGMetric.TestC0 → ℝ) where
  toEquiv :=
    { toFun := fun F φ => F (meanZeroTestEquiv φ)
      invFun := fun F φ => F (meanZeroTestEquiv.symm φ)
      left_inv := by intro F; funext φ; simp
      right_inv := by intro F; funext φ; simp }
  measurable_toFun := measurable_pi_iff.mpr fun φ => measurable_pi_apply (meanZeroTestEquiv φ)
  measurable_invFun := measurable_pi_iff.mpr fun φ => measurable_pi_apply (meanZeroTestEquiv.symm φ)

/-- The field reindexing maps raw GFF pairings to the existing bundled
pairing process. -/
theorem meanZeroFieldEquiv_pairings {Ω : Type*}
    (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    meanZeroFieldEquiv (fun φ => hC ω φ.1) = Section6.pairingProc hC ω := rfl

/-- Reindexing commutes with the whole-plane logarithmic insertion. -/
theorem meanZeroFieldEquiv_root_insertion {Ω : Type*}
    (hC : Ω → (ℂ → ℝ) → ℝ) (γ : ℝ) (ω : Ω) (z : ℂ) :
    meanZeroFieldEquiv (fun φ => hC ω φ.1 + ∫ x, φ.1 x *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
    (fun φ : LQGMetric.TestC0 => hC ω φ.1 + ∫ x, φ.1 x *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) := rfl

/-- The whole-plane inserted GFF in raw test coordinates is jointly
measurable in the root and field. -/
theorem IsWholePlaneGFF.measurable_raw_root_inserted_pairings
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    Measurable (fun p : ℂ × Ω => fun φ : RawMeanZeroTest =>
      hC p.2 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))) := by
  convert meanZeroFieldEquiv.symm.measurable.comp
    (hh.measurable_wholePlane_inserted_pairings γ) using 1
  funext p φ
  rfl

/-- The field-first inserted law in raw coordinates becomes the Section 8
reference law after reindexing its field coordinate. -/
theorem IsWholePlaneGFF.map_raw_root_insertion_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (ρ : Measure ℂ) [SFinite ρ] :
    ((P.prod ρ).map (fun p : Ω × ℂ =>
      ((fun φ : RawMeanZeroTest => hC p.1 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.2‖ + γ * Real.log (max ‖x‖ 1))), p.2))).map
      (fun q => (meanZeroFieldEquiv q.1, q.2)) =
    shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
      hC p.2 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))) := by
  have hmap : Measurable (fun q : (RawMeanZeroTest → ℝ) × ℂ =>
      (meanZeroFieldEquiv q.1, q.2)) :=
    (meanZeroFieldEquiv.measurable.comp measurable_fst).prodMk measurable_snd
  have hraw : Measurable (fun p : Ω × ℂ =>
      ((fun φ : RawMeanZeroTest => hC p.1 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.2‖ + γ * Real.log (max ‖x‖ 1))), p.2)) :=
    (hh.measurable_raw_root_inserted_pairings γ |>.comp measurable_swap).prodMk measurable_snd
  rw [Measure.map_map hmap hraw,
    shiftedRootReferenceLaw_eq_field_first ρ P _ (hh.measurable_wholePlane_inserted_pairings γ)]
  rfl

#print axioms meanZeroTestEquiv
#print axioms meanZeroFieldEquiv
#print axioms meanZeroFieldEquiv_pairings
#print axioms meanZeroFieldEquiv_root_insertion
#print axioms IsWholePlaneGFF.measurable_raw_root_inserted_pairings
#print axioms IsWholePlaneGFF.map_raw_root_insertion_law

end HarmonicBalls
