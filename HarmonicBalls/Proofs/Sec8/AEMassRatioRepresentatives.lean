import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios
import Mathlib.MeasureTheory.SetAlgebra

/-! # Normalized restrictions from local mass-ratio versions -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

open Classical in
/-- Countably many normalized mass-ratio versions determine a measurable
normalized restriction when each exceptional set has a measurable null
envelope in the specified local sigma-algebra. -/
theorem exists_normalizedRestriction_version_of_piSystem_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (μ : Ω → Measure ℂ) (U : Set ℂ)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (hratio : ∀ V ∈ S, ∃ (Y : Ω → ℝ≥0∞) (E : Set Ω),
      @Measurable Ω ℝ≥0∞ m _ Y ∧ MeasurableSet[m] E ∧ P Eᶜ = 0 ∧
      ∀ ω ∈ E, μ ω (V ∩ U) / μ ω U = Y ω) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  let : Countable S := hcount.to_subtype
  have hr : ∀ v : S, ∃ (Y : Ω → ℝ≥0∞) (E : Set Ω),
      @Measurable Ω ℝ≥0∞ m _ Y ∧ MeasurableSet[m] E ∧ P Eᶜ = 0 ∧
      ∀ ω ∈ E, μ ω (v.1 ∩ U) / μ ω U = Y ω := fun v => hratio v.1 v.2
  choose Y E hYm hEm hEzero hEq using hr
  let F : Set Ω := ⋂ v : S, E v
  have hFm : MeasurableSet[m] F := MeasurableSet.iInter hEm
  have hFae : ∀ᵐ ω ∂P, ω ∈ F := by
    have hh : ∀ v : S, ∀ᵐ ω ∂P, ω ∈ E v := fun v => ae_iff.mpr (hEzero v)
    filter_upwards [ae_all_iff.mpr hh] with ω hω
    exact mem_iInter.mpr hω
  let ν : Ω → Measure ℂ := fun ω => if ω ∈ F then normalizedRestriction (μ ω) U else 0
  have hmass : ∀ V ∈ S, @Measurable Ω ℝ≥0∞ m _ (fun ω => ν ω V) := by
    intro V hV
    let v : S := ⟨V, hV⟩
    have hm := (hYm v).indicator hFm
    convert hm using 1
    ext ω
    by_cases hω : ω ∈ F
    · have he := hEq v ω ((mem_iInter.mp hω) v)
      simpa only [ν, hω, ↓reduceIte, indicator_of_mem, normalizedRestriction,
        Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hsets V hV),
        ENNReal.div_eq_inv_mul] using he
    · simp [ν, hω]
  refine ⟨ν, ?_, ?_⟩
  · let : MeasurableSpace Ω := m
    have (ω : Ω) : IsFiniteMeasure (ν ω) := by
      dsimp only [ν]
      split_ifs <;> infer_instance
    exact Measurable.measure_of_isPiSystem hgen hpi hmass (hmass univ huniv)
  · filter_upwards [hFae] with ω hω
    simp only [ν, hω, ↓reduceIte]

/-- The complex plane has a countable open generating π-system containing
its whole space. -/
theorem exists_countable_open_piSystem_complex :
    ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧
      (∀ V ∈ S, IsOpen V) ∧ univ ∈ S ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S := by
  let B : Set (Set ℂ) := TopologicalSpace.countableBasis ℂ ∪ {univ}
  let S := generatePiSystem B
  have hBcount : B.Countable :=
    (TopologicalSpace.countable_countableBasis ℂ).union (countable_singleton univ)
  have hBopen : ∀ V ∈ B, IsOpen V := by
    intro V hV
    rcases hV with hV | hV
    · exact (TopologicalSpace.isBasis_countableBasis ℂ).isOpen hV
    · simpa only [mem_singleton_iff] using hV ▸ isOpen_univ
  have hSopen : ∀ V ∈ S, IsOpen V := by
    exact generatePiSystem_min hBopen isPiSystem_isOpen
  have hSalg : S ⊆ generateSetAlgebra B := by
    apply generatePiSystem_min self_subset_generateSetAlgebra
    intro V hV W hW _
    exact isSetAlgebra_generateSetAlgebra.inter_mem hV hW
  have hSgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S := by
    apply le_antisymm
    · calc
        (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
        _ = MeasurableSpace.generateFrom (TopologicalSpace.countableBasis ℂ) :=
          (TopologicalSpace.isBasis_countableBasis ℂ).borel_eq_generateFrom
        _ ≤ MeasurableSpace.generateFrom S := MeasurableSpace.generateFrom_mono (fun V hV =>
          subset_generatePiSystem_self B (Or.inl hV))
    · exact MeasurableSpace.generateFrom_le (fun V hV => (hSopen V hV).measurableSet)
  exact ⟨S, (countable_generateSetAlgebra hBcount).mono hSalg,
    isPiSystem_generatePiSystem B, hSopen, subset_generatePiSystem_self B (Or.inr rfl), hSgen⟩

/-- Germ-measurable normalized mass-ratio versions on open sets give a
measure-valued version if their exceptional sets have germ-measurable null
envelopes. -/
theorem exists_normalizedRestriction_version_of_open_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (μ : Ω → Measure ℂ) (U : Set ℂ)
    (hratio : ∀ V : Set ℂ, IsOpen V → ∃ (Y : Ω → ℝ≥0∞) (E : Set Ω),
      @Measurable Ω ℝ≥0∞ m _ Y ∧ MeasurableSet[m] E ∧ P Eᶜ = 0 ∧
      ∀ ω ∈ E, μ ω (V ∩ U) / μ ω U = Y ω) :
    ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) U := by
  obtain ⟨S, hcount, hpi, hopen, huniv, hgen⟩ := exists_countable_open_piSystem_complex
  refine @exists_normalizedRestriction_version_of_piSystem_ratios Ω mΩ P m μ U S hcount hgen hpi
    (fun V hV => (hopen V hV).measurableSet) huniv ?_
  intro V hV
  exact hratio V (hopen V hV)

end HarmonicBalls
