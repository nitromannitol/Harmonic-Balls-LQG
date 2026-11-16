import HarmonicBalls.Defs.HarmonicBall
import Mathlib.MeasureTheory.Measure.Support

/-! # Compact support of locally finite Green sources

Locally finite measures on the plane whose supports lie in a bounded set have finite mass.
Their Green potentials belong to the compact-source test class when their supports avoid the
specified domain.
-/

namespace HarmonicBalls

open MeasureTheory

/-- Locally finite sources with support in a bounded set give a compactly supported
Green-potential test. -/
theorem greenPotentialClass_of_locallyFinite_support {O D : Set ℂ} (hO : Bornology.IsBounded O)
    (ν₁ ν₂ : Measure ℂ) [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
    (h₁ : ν₁.support ⊆ O \ D) (h₂ : ν₂.support ⊆ O \ D) :
    greenPotential O ν₁ - greenPotential O ν₂ ∈ greenPotentialClass O D := by
  let K := ν₁.support ∪ ν₂.support
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact Measure.isClosed_support.union Measure.isClosed_support
    · exact hO.subset (Set.union_subset (h₁.trans Set.sdiff_subset) (h₂.trans Set.sdiff_subset))
  have hk₁ : ν₁ Kᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left)
    Measure.measure_compl_support
  have hk₂ : ν₂ Kᶜ = 0 := measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_right)
    Measure.measure_compl_support
  have hfin₁ : IsFiniteMeasure ν₁ := ⟨by
    rw [← measure_congr (ae_eq_univ.mpr (ae_iff.mpr hk₁))]
    exact hK.measure_lt_top⟩
  have hfin₂ : IsFiniteMeasure ν₂ := ⟨by
    rw [← measure_congr (ae_eq_univ.mpr (ae_iff.mpr hk₂))]
    exact hK.measure_lt_top⟩
  exact ⟨K, ν₁, ν₂, hK, Set.union_subset h₁ h₂, hfin₁, hfin₂, hk₁, hk₂, rfl⟩

/-- The compact-source mean value property applies to locally finite sources whose global
supports lie in the prescribed bounded region. -/
theorem IsHarmonicBallGen.meanValue_of_locallyFinite_support {μ : Measure ℂ} {Λ O : Set ℂ}
    {z : ℂ} (hball : IsHarmonicBallGen μ Λ z) (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (hΛO : closure Λ ⊆ O)
    (ν₁ ν₂ : Measure ℂ) [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₂]
    (h₁ : ν₁.support ⊆ O \ Λ) (h₂ : ν₂.support ⊆ O \ Λ)
    (f : ℂ → ℝ) (hf : InnerProductSpace.HarmonicOnNhd f (closure Λ)) :
    HasMeanValueProperty μ Λ z (f + (greenPotential O ν₁ - greenPotential O ν₂)) := by
  apply hball.2
  exact ⟨f, greenPotential O ν₁ - greenPotential O ν₂, O, hf, hO, hOb, hΛO,
    greenPotentialClass_of_locallyFinite_support hOb ν₁ ν₂ h₁ h₂, rfl⟩

end HarmonicBalls
