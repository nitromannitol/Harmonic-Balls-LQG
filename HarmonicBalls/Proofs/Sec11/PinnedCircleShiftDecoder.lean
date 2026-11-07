import HarmonicBalls.Proofs.Sec11.JointSmoothShiftCircle

/-! # Pinned unit-circle observables under field shifts

The whole-plane normalization removes the reference circle from the local
centered-circle decoder. The imported Section 8 development uses Leonardo
Bonanno's `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric

namespace HarmonicBalls

/-- At unit radius the whole-plane normalization turns centered circle
averages into absolute circle averages, simultaneously for all centers and
all continuous shifts preserving the unit-circle normalization. -/
theorem IsWholePlaneGFF.exists_joint_pinned_unit_circle_shift_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∃ F : (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        ∀ z, closedBall z 1 ⊆ ball 0 ε →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) z =
          fieldCircleAverage α (hcirc ω) 1 z + Real.circleAverage g z 1 := by
  obtain ⟨F, hF, hFcorrect⟩ :=
    hGFF.exists_joint_local_singular_circle_shift_decoder (α := α) (ε := ε) one_pos
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFcorrect, hGFF.ae_circleAverage_one_zero] with ω hcorrect hpin
  intro g hg hgpin z hz
  have href : fieldCircleAverage α (hcirc ω) 1 0 = 0 := by
    rw [fieldCircleAverage_eq α (hcirc ω) one_pos 0, hpin]
    simp
  simpa [href, hgpin] using hcorrect g hg z hz

#print axioms IsWholePlaneGFF.exists_joint_pinned_unit_circle_shift_decoder

end HarmonicBalls
