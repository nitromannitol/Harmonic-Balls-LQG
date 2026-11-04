import HarmonicBalls.Proofs.Sec8.RootedShiftMeasurability

/-! # Measurability of the whole-plane rooted insertion

The logarithmic insertion in the whole-plane rooted-field formula is jointly
measurable in the sampled point and the field, including at the singularity.
No rooted-field change-of-measure formula is assumed here. The imported Section 6
development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- The whole-plane logarithmic insertion, with the unit-circle normalization
term, is jointly measurable in the root and the spatial variable. -/
theorem measurable_wholePlane_root_insertion (γ : ℝ) :
    Measurable (fun p : ℂ × ℂ =>
      -γ * Real.log ‖p.2 - p.1‖ + γ * Real.log (max ‖p.2‖ 1)) := by
  have hdiff : Measurable (fun p : ℂ × ℂ => p.2 - p.1) :=
    measurable_snd.sub measurable_fst
  exact ((Real.measurable_log.comp hdiff.norm).const_mul (-γ)).add
    ((Real.measurable_log.comp (measurable_snd.norm.max measurable_const)).const_mul γ)

/-- The whole-plane insertion defines a jointly measurable process on all
mean-zero test functions. -/
theorem measurable_wholePlane_inserted_pairings
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X) (γ : ℝ) :
    Measurable (fun p : ℂ × Ω => fun φ : LQGMetric.TestC0 =>
      X p.2 φ + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact (((measurable_pi_apply φ).comp hX).comp measurable_snd).add
    ((measurable_integral_test_mul_root_function
      (fun z x => -γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))
      (measurable_wholePlane_root_insertion γ) φ.1).comp measurable_fst)

/-- The whole-plane GFF assumptions provide the measurable pairing process
needed for the rooted logarithmic insertion. -/
theorem IsWholePlaneGFF.measurable_wholePlane_inserted_pairings
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    Measurable (fun p : ℂ × Ω => fun φ : LQGMetric.TestC0 =>
      hC p.2 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))) :=
  HarmonicBalls.measurable_wholePlane_inserted_pairings (Section6.pairingProc hC)
    (Section6.measurable_pairingProc hh) γ

/-- Swapping the independent field and root identifies the two standard
conventions for a rooted reference law. -/
theorem shiftedRootReferenceLaw_eq_field_first
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) [SFinite ρ] [SFinite P]
    (shift : Z × Ω → F) (hshift : Measurable shift) :
    shiftedRootReferenceLaw ρ P shift =
      (P.prod ρ).map (fun p => (shift (p.2, p.1), p.2)) := by
  unfold shiftedRootReferenceLaw
  rw [← Measure.prod_swap (μ := P) (ν := ρ), Measure.map_map]
  · rfl
  · exact hshift.prodMk measurable_fst
  · exact measurable_swap

#print axioms measurable_wholePlane_root_insertion
#print axioms measurable_wholePlane_inserted_pairings
#print axioms IsWholePlaneGFF.measurable_wholePlane_inserted_pairings
#print axioms shiftedRootReferenceLaw_eq_field_first

end HarmonicBalls
