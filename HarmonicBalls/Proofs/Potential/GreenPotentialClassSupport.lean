import HarmonicBalls.Defs.HarmonicBall

/-!
# The class of Green potentials of signed Radon measures supported in `O \ D`

The enlarged test class of Theorem 1.1 (eq:harmonic-fns, corrected paper lines 136-146) consists of
the Green potentials `∫_O G_O(·, y) ν(dy)` of signed Radon measures `ν` with support in `O \ D`, for
bounded open `O, D`. A signed Radon measure is a difference `ν = ν₁ - ν₂` of Radon (locally finite)
measures, and its support is the smallest closed subset of `ℂ` off which `ν₁` and `ν₂` vanish.
`radonGreenPotentialClass O D` is this class: Green potentials of differences of locally finite
measures vanishing off a closed set `S ⊆ O \ D`.

`greenPotentialClass O D` (`Defs/HarmonicBall.lean`) uses finite measures concentrated on a compact
set `K ⊆ O \ D`. For bounded `O` the two classes are equal (`radonGreenPotentialClass_eq`): a closed
subset of the bounded set `O` is compact, and a locally finite measure vanishing off a compact set is
finite.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- The Green potentials `G_O ν₁ - G_O ν₂` of differences of locally finite (Radon) measures `ν₁, ν₂`
vanishing off a closed subset `S` of `O \ D` of `ℂ`: the class `H̃_O(D)` of eq:harmonic-fns, with the
support of the signed Radon measure taken as a closed subset of `ℂ`. -/
def radonGreenPotentialClass (O D : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (S : Set ℂ) (ν₁ ν₂ : Measure ℂ), IsClosed S ∧ S ⊆ O \ D ∧ IsLocallyFiniteMeasure ν₁ ∧
    IsLocallyFiniteMeasure ν₂ ∧ ν₁ Sᶜ = 0 ∧ ν₂ Sᶜ = 0 ∧ f = greenPotential O ν₁ - greenPotential O ν₂}

/-- A locally finite measure vanishing off a compact set is finite. -/
theorem isFiniteMeasure_of_compl_eq_zero {ν : Measure ℂ} [IsLocallyFiniteMeasure ν] {K : Set ℂ}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) : IsFiniteMeasure ν := by
  refine ⟨?_⟩
  calc ν univ ≤ ν K + ν Kᶜ := by
        rw [← union_compl_self K]
        exact measure_union_le _ _
    _ < ⊤ := by rw [hν, add_zero]; exact hK.measure_lt_top

/-- **The test class of Theorem 1.1 with signed Radon measures equals the formal one**: for bounded
`O`, the Green potentials of signed Radon measures supported in `O \ D` are exactly the Green
potentials of differences of finite measures concentrated on a compact subset of `O \ D`. -/
theorem radonGreenPotentialClass_eq {O : Set ℂ} (hO : Bornology.IsBounded O) (D : Set ℂ) :
    radonGreenPotentialClass O D = greenPotentialClass O D := by
  ext f
  constructor
  · rintro ⟨S, ν₁, ν₂, hS, hSO, h₁, h₂, hν₁, hν₂, rfl⟩
    have hSc : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded hS (hO.subset (hSO.trans sdiff_subset))
    exact ⟨S, ν₁, ν₂, hSc, hSO, isFiniteMeasure_of_compl_eq_zero hSc hν₁,
      isFiniteMeasure_of_compl_eq_zero hSc hν₂, hν₁, hν₂, rfl⟩
  · rintro ⟨K, ν₁, ν₂, hK, hKO, h₁, h₂, hν₁, hν₂, rfl⟩
    exact ⟨K, ν₁, ν₂, hK.isClosed, hKO, inferInstance, inferInstance, hν₁, hν₂, rfl⟩

end HarmonicBalls
