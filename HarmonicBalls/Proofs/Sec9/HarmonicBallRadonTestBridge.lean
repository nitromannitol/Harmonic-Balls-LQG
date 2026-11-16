import HarmonicBalls.Defs.HarmonicBall
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

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

/-- A signed source with integrable Green kernels has a compact-source representation. -/
theorem signed_greenPotential_mem_greenPotentialClass_of_integrable
    {O D : Set ℂ} (hO : Bornology.IsBounded O) (ν : SignedMeasure ℂ)
    (hs : ν.variation.support ⊆ O \ D)
    (hi : ∀ x, Integrable (fun y => greenFunction O x y) ν.variation) :
    (fun x => ∫ᵛ y, greenFunction O x y ∂<•ν) ∈ greenPotentialClass O D := by
  let ν₁ := ν.toJordanDecomposition.posPart
  let ν₂ := ν.toJordanDecomposition.negPart
  have hv : ν.variation = ν₁ + ν₂ := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    rfl
  have hle₁ : ν₁ ≤ ν.variation := by rw [hv]; exact Measure.le_add_right le_rfl
  have hle₂ : ν₂ ≤ ν.variation := by rw [hv]; exact Measure.le_add_left le_rfl
  have hp₁ : ν₁.support ⊆ O \ D := (Measure.support_mono hle₁).trans hs
  have hp₂ : ν₂.support ⊆ O \ D := (Measure.support_mono hle₂).trans hs
  have heq : (fun x => ∫ᵛ y, greenFunction O x y ∂<•ν) =
      greenPotential O ν₁ - greenPotential O ν₂ := by
    funext x
    have hi₁ : Integrable (fun y => greenFunction O x y) ν₁ := (hi x).mono_measure hle₁
    have hi₂ : Integrable (fun y => greenFunction O x y) ν₂ := (hi x).mono_measure hle₂
    have hv₁ : ν₁.toSignedMeasure.Integrable (fun y => greenFunction O x y) := by
      simpa [VectorMeasure.Integrable] using hi₁
    have hv₂ : ν₂.toSignedMeasure.Integrable (fun y => greenFunction O x y) := by
      simpa [VectorMeasure.Integrable] using hi₂
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν]
    change (∫ᵛ y, greenFunction O x y ∂<•(ν₁.toSignedMeasure - ν₂.toSignedMeasure)) = _
    rw [VectorMeasure.integral_sub_vectorMeasure hv₁ hv₂]
    simp [greenPotential]
  rw [heq]
  exact greenPotentialClass_of_locallyFinite_support hO ν₁ ν₂ hp₁ hp₂

/-- Signed Green potentials with global support outside the ball satisfy its mean value
property. -/
theorem IsHarmonicBallGen.meanValue_signed_greenPotential {μ : Measure ℂ} {Λ O : Set ℂ}
    {z : ℂ} (hball : IsHarmonicBallGen μ Λ z) (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (hΛO : closure Λ ⊆ O) (ν : SignedMeasure ℂ)
    (hs : ν.variation.support ⊆ O \ Λ) (f : ℂ → ℝ)
    (hf : InnerProductSpace.HarmonicOnNhd f (closure Λ)) :
    HasMeanValueProperty μ Λ z (f + fun x => ∫ᵛ y, greenFunction O x y ∂<•ν) := by
  let ν₁ := ν.toJordanDecomposition.posPart
  let ν₂ := ν.toJordanDecomposition.negPart
  have hv : ν.variation = ν₁ + ν₂ := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    rfl
  have hle₁ : ν₁ ≤ ν.variation := by rw [hv]; exact Measure.le_add_right le_rfl
  have hle₂ : ν₂ ≤ ν.variation := by rw [hv]; exact Measure.le_add_left le_rfl
  have hp₁ : ν₁.support ⊆ O \ Λ := (Measure.support_mono hle₁).trans hs
  have hp₂ : ν₂.support ⊆ O \ Λ := (Measure.support_mono hle₂).trans hs
  have : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hK : IsCompact ν.variation.support := Metric.isCompact_of_isClosed_isBounded
    Measure.isClosed_support (hOb.subset (hs.trans Set.sdiff_subset))
  have hEq : Set.EqOn (fun x => f x + (greenPotential O ν₁ x - greenPotential O ν₂ x))
      (fun x => f x + ∫ᵛ y, greenFunction O x y ∂<•ν) Λ := by
    intro x hx
    have hi : Integrable (greenFunction O x) ν.variation :=
      greenFunctionIntegrableAwayFromPoleStep_holds O ν.variation.support x ν.variation hO
        (hΛO (subset_closure hx)) hK (hs.trans Set.sdiff_subset)
        (fun hxK => (hs hxK).2 hx) inferInstance Measure.measure_compl_support
    have hv₁ : ν₁.toSignedMeasure.Integrable (greenFunction O x) := by
      simpa [VectorMeasure.Integrable] using hi.mono_measure hle₁
    have hv₂ : ν₂.toSignedMeasure.Integrable (greenFunction O x) := by
      simpa [VectorMeasure.Integrable] using hi.mono_measure hle₂
    change f x + (greenPotential O ν₁ x - greenPotential O ν₂ x) =
      f x + ∫ᵛ y, greenFunction O x y ∂<•ν
    congr 1
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν]
    change _ = (∫ᵛ y, greenFunction O x y ∂<•(ν₁.toSignedMeasure - ν₂.toSignedMeasure))
    rw [VectorMeasure.integral_sub_vectorMeasure hv₁ hv₂]
    simp [greenPotential]
  have hmv := hball.meanValue_of_locallyFinite_support hO hOb hΛO ν₁ ν₂ hp₁ hp₂ f hf
  constructor
  · exact hmv.1.congr_fun hEq hball.1.1.measurableSet
  · change (fun x => f x + ∫ᵛ y, greenFunction O x y ∂<•ν) z * μ.real Λ =
      ∫ x in Λ, (fun x => f x + ∫ᵛ y, greenFunction O x y ∂<•ν) x ∂μ
    rw [← hEq hball.1.2.1, ← setIntegral_congr_fun hball.1.1.measurableSet hEq]
    exact hmv.2

end HarmonicBalls
