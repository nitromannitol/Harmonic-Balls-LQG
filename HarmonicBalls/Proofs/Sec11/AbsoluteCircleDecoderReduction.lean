import HarmonicBalls.Proofs.Sec11.JointSmoothShiftCircle

/-! # Reduction of absolute circle decoders to radial references

Spatially centered decoders reconstruct all centers once the circle average
at the origin is reconstructed at each radius. The imported Section 8
development uses Leonardo Bonanno's `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`
formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric

namespace HarmonicBalls

/-- A countable family of radial reference decoders yields jointly measurable
absolute circle-average decoders at all buffered centers. The common event is
valid for every continuous shift preserving the pinned unit-circle average. -/
theorem IsWholePlaneGFF.exists_joint_absolute_circle_shift_decoders_of_radial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (R : ℕ → (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℝ)
    (hRm : ∀ n, Measurable (R n))
    (hR : ∀ᵐ ω ∂P, ∀ n (g : ℂ → ℝ), Continuous g → Real.circleAverage g 0 1 = 0 →
      R n (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) =
        fieldCircleAverage α (hcirc ω) (r n) 0 + Real.circleAverage g 0 (r n)) :
    ∃ D : ℕ → (LocalZeroMeanTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      (∀ n, Measurable (Function.uncurry (D n))) ∧
      ∀ᵐ ω ∂P, ∀ n (g : ℂ → ℝ), Continuous g → Real.circleAverage g 0 1 = 0 → ∀ z,
        closedBall z (r n) ⊆ ball 0 ε →
        D n (localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω) z =
          fieldCircleAverage α (hcirc ω) (r n) z + Real.circleAverage g z (r n) := by
  choose C hCm hCe using fun n =>
    hGFF.exists_joint_local_singular_circle_shift_decoder (α := α) (ε := ε) (hr n)
  refine ⟨fun n v z => C n v z + R n v, ?_, ?_⟩
  · intro n
    exact (hCm n).add ((hRm n).comp measurable_fst)
  · filter_upwards [ae_all_iff.mpr hCe, hR] with ω hCω hRω n g hg hpin z hz
    rw [hCω n g hg z hz, hRω n g hg hpin]
    ring


end HarmonicBalls
