import HarmonicBalls.Defs.Notation

/-!
# Mass of the increment of a cluster

The measure-theoretic step in Proposition 7.2: the mass of the increment of
two nested clusters bounds the mass of the later cluster on an annulus which
misses the earlier cluster. The exact mass identity and monotonicity are kept
as explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- For nested sets, the mass of the increment is at most the excess in their
masses. The earlier set must be null-measurable and have finite mass. -/
theorem measure_sdiff_le_of_measure_le_add {μ : Measure ℂ} {A B : Set ℂ} {ε : ℝ≥0∞}
    (hAB : A ⊆ B) (hA : NullMeasurableSet A μ) (hAfin : μ A ≠ ∞)
    (hmass : μ B ≤ μ A + ε) : μ (B \ A) ≤ ε := by
  exact (measure_sdiff_le_iff_le_add hA hAB hAfin).2 hmass

/-- An annulus avoiding the earlier cluster sees at most the mass increment. -/
theorem measure_inter_le_of_disjoint_of_measure_le_add
    {μ : Measure ℂ} {A B U : Set ℂ} {ε : ℝ≥0∞}
    (hAB : A ⊆ B) (hA : NullMeasurableSet A μ) (hAfin : μ A ≠ ∞)
    (hmass : μ B ≤ μ A + ε) (hdisjoint : Disjoint U A) :
    μ (B ∩ U) ≤ ε := by
  calc
    μ (B ∩ U) ≤ μ (B \ A) := measure_mono (by
      intro x hx
      exact ⟨hx.1, fun hxA => Set.disjoint_left.1 hdisjoint hx.2 hxA⟩)
    _ ≤ ε := measure_sdiff_le_of_measure_le_add hAB hA hAfin hmass

end HarmonicBalls
