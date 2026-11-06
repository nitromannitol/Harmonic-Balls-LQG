import HarmonicBalls.Proofs.Sec6.LocalRelativeCollar

/-! # Mass normalization and rooted law comparison

A scale-independent absolute-continuity modulus for the complete law of a
measure is not implied by positivity and finiteness of an arbitrary mass
normalization. Relative collar events themselves are invariant under such
normalizations. The imported Section 6 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

/-- Even with a fixed spatial scale and a deterministic finite reference
measure, arbitrary positive finite normalizations need not give a uniformly
absolutely continuous family of measure laws. -/
theorem arbitrary_mass_normalization_not_uniformly_absolutelyContinuous :
    ¬ ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ (n : ℕ) (E : Set (Measure ℂ)), MeasurableSet E →
        Measure.dirac (Measure.dirac (0 : ℂ)) E ≤ δ →
        Measure.dirac (((n + 1 : ℕ) : ℝ≥0∞) • Measure.dirac (0 : ℂ)) E ≤ ε := by
  intro h
  obtain ⟨δ, hδ, hδbound⟩ := h (1 / 2) (by norm_num)
  let E : Set (Measure ℂ) := {μ | μ univ ≠ 1}
  have hE : MeasurableSet E := (Measure.measurable_coe MeasurableSet.univ)
    (measurableSet_singleton 1) |>.compl
  have hzero : Measure.dirac (Measure.dirac (0 : ℂ)) E ≤ δ := by
    rw [Measure.dirac_apply' _ hE]
    simp [E]
  have hbound := hδbound 1 E hE hzero
  rw [Measure.dirac_apply' _ hE] at hbound
  norm_num [E, Measure.smul_apply] at hbound

end HarmonicBalls.Section6
