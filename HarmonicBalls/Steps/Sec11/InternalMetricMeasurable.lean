import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of internal-distance extrema

Pointwise measurability and the deterministic continuity of internal distance
imply measurability of extrema over arbitrary subsets of an open domain.
-/

namespace HarmonicBalls

open Set MeasureTheory Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The supremum of a random internal distance over two fixed subsets of an
open domain is measurable when every pointwise distance is measurable. -/
theorem measurable_iSup_internalMetric
    {D : Ω → ℂ → ℂ → ℝ} {V A B : Set ℂ} (hV : IsOpen V)
    (hA : A ⊆ V) (hB : B ⊆ V)
    (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω x y, 0 ≤ D ω x y)
    (hmeas : ∀ x ∈ A, ∀ y ∈ B, Measurable fun ω => internalMetric (D ω) V x y) :
    Measurable fun ω => ⨆ x ∈ A, ⨆ y ∈ B, internalMetric (D ω) V x y := by
  let f : A × B → Ω → ℝ≥0∞ := fun p ω => internalMetric (D ω) V p.1 p.2
  have hf (ω : Ω) : Continuous (fun p : A × B => f p ω) := by
    have hc : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (hD ω).continuousOn_internalMetric_pair (hnonneg ω) hV |>.comp_continuous hc
      (fun p => ⟨hA p.1.property, hB p.2.property⟩)
  have hm : Measurable (⨆ p : A × B, f p) :=
    measurable_iSup_of_lowerSemicontinuous (fun p => hmeas p.1 p.1.property p.2 p.2.property)
      (fun ω => (hf ω).lowerSemicontinuous)
  convert hm using 1
  ext ω
  simp only [iSup_apply, f, iSup_subtype, iSup_prod]

/-- The infimum of a random internal distance over two fixed subsets of an
open domain is measurable when every pointwise distance is measurable. -/
theorem measurable_iInf_internalMetric
    {D : Ω → ℂ → ℂ → ℝ} {V A B : Set ℂ} (hV : IsOpen V)
    (hA : A ⊆ V) (hB : B ⊆ V)
    (hD : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ ω x y, 0 ≤ D ω x y)
    (hmeas : ∀ x ∈ A, ∀ y ∈ B, Measurable fun ω => internalMetric (D ω) V x y) :
    Measurable fun ω => ⨅ x ∈ A, ⨅ y ∈ B, internalMetric (D ω) V x y := by
  let f : A × B → Ω → ℝ≥0∞ := fun p ω => internalMetric (D ω) V p.1 p.2
  have hf (ω : Ω) : Continuous (fun p : A × B => f p ω) := by
    have hc : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (hD ω).continuousOn_internalMetric_pair (hnonneg ω) hV |>.comp_continuous hc
      (fun p => ⟨hA p.1.property, hB p.2.property⟩)
  have hm : Measurable (⨅ p : A × B, f p) :=
    measurable_iInf_of_upperSemicontinuous (fun p => hmeas p.1 p.1.property p.2 p.2.property)
      (fun ω => (hf ω).upperSemicontinuous)
  convert hm using 1
  ext ω
  simp only [iInf_apply, f, iInf_subtype, iInf_prod]

end HarmonicBalls
