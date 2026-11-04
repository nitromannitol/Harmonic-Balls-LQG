import HarmonicBalls.Proofs.Sec8.CommonApproximationLaw
import HarmonicBalls.Proofs.Sec8.AEMassRatioRepresentatives

/-! # Finite-measure laws from common mass approximations

A countable generating π-system supplies enough scalar observables to
transfer the law of an entire finite measure.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The real masses on a countable generating π-system determine the law of
finite random measures. The common approximants and field-law domination are
explicit hypotheses. -/
theorem finiteMeasure_law_absolutelyContinuous_of_common_approximations
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (U : Ω → {μ : Measure ℂ // IsFiniteMeasure μ})
    (V : Ξ → {μ : Measure ℂ // IsFiniteMeasure μ})
    (hU : Measurable U) (hV : Measurable V)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → E → ℝ) (hf : ∀ A n, Measurable (f A n))
    (hu : ∀ A, TendstoInMeasure P (fun n ω => f A n (X ω)) atTop
      (fun ω => ((U ω).val A.val).toReal))
    (hv : ∀ A, TendstoInMeasure Q (fun n ω => f A n (Y ω)) atTop
      (fun ω => ((V ω).val A.val).toReal)) :
    Q.map (fun ω => (V ω).val) ≪ P.map (fun ω => (U ω).val) := by
  let : Countable S := hcount.to_subtype
  let L := {μ : Measure ℂ // IsFiniteMeasure μ}
  let encode : L → S → ℝ := fun μ A => (μ.val A.val).toReal
  have hencode : Measurable encode := by
    apply Measurable.of_eval
    intro A
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_coe (hsets A.val A.property)).comp measurable_subtype_coe)
  have hdom' : Q.map (encode ∘ V) ≪ P.map (encode ∘ U) := by
    exact countable_limit_law_absolutelyContinuous P Q X Y hX hY hdom f hf
      (fun A ω => ((U ω).val A.val).toReal)
      (fun A ω => ((V ω).val A.val).toReal) hu hv
  let m : MeasurableSpace L := MeasurableSpace.comap encode inferInstance
  have hcoe : @Measurable L (Measure ℂ) m _ Subtype.val := by
    let : MeasurableSpace L := m
    let (μ : L) : IsFiniteMeasure μ.val := μ.property
    apply Measurable.measure_of_isPiSystem hgen hpi
    · intro A hA
      have hm : Measurable (fun μ : L => ENNReal.ofReal (encode μ ⟨A, hA⟩)) :=
        ENNReal.measurable_ofReal.comp ((measurable_pi_apply (⟨A, hA⟩ : S)).comp
          (comap_measurable encode))
      convert hm using 1
      funext μ
      exact (ENNReal.ofReal_toReal (measure_ne_top μ.val A)).symm
    · have hm : Measurable (fun μ : L => ENNReal.ofReal (encode μ ⟨univ, huniv⟩)) :=
        ENNReal.measurable_ofReal.comp ((measurable_pi_apply (⟨univ, huniv⟩ : S)).comp
          (comap_measurable encode))
      convert hm using 1
      funext μ
      exact (ENNReal.ofReal_toReal (measure_ne_top μ.val univ)).symm
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hz
  obtain ⟨B, hB, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hcoe hA)
  have hpreU : (encode ∘ U) ⁻¹' B = (fun ω => (U ω).val) ⁻¹' A := by
    ext ω
    exact Set.ext_iff.mp heq (U ω)
  have hpreV : (encode ∘ V) ⁻¹' B = (fun ω => (V ω).val) ⁻¹' A := by
    ext ω
    exact Set.ext_iff.mp heq (V ω)
  have heU : P ((fun ω => (U ω).val) ⁻¹' A) = (P.map (fun ω => (U ω).val)) A := by
    symm
    exact Measure.map_apply (measurable_subtype_coe.comp hU) hA
  have heV : Q ((fun ω => (V ω).val) ⁻¹' A) = (Q.map (fun ω => (V ω).val)) A := by
    symm
    exact Measure.map_apply (measurable_subtype_coe.comp hV) hA
  have hz' : P.map (encode ∘ U) B = 0 := by
    rw [Measure.map_apply (hencode.comp hU) hB, hpreU, heU]
    exact hz
  have hq := hdom' hz'
  rwa [Measure.map_apply (hencode.comp hV) hB, hpreV, heV] at hq


/-- Common approximations to normalized masses on a countable generating
π-system transfer the law of the normalized restrictions themselves. -/
theorem normalizedRestriction_law_absolutelyContinuous_of_common_approximations
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (hμ : Measurable μ) (hν : Measurable ν)
    (W : Set ℂ) (hW : MeasurableSet W)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → E → ℝ) (hf : ∀ A n, Measurable (f A n))
    (hu : ∀ A, TendstoInMeasure P (fun n ω => f A n (X ω)) atTop
      (fun ω => (normalizedRestriction (μ ω) W A.val).toReal))
    (hv : ∀ A, TendstoInMeasure Q (fun n ω => f A n (Y ω)) atTop
      (fun ω => (normalizedRestriction (ν ω) W A.val).toReal)) :
    Q.map (fun ω => normalizedRestriction (ν ω) W) ≪
      P.map (fun ω => normalizedRestriction (μ ω) W) := by
  have hnorm : Measurable (fun η : Measure ℂ => normalizedRestriction η W) := by
    apply measurable_normalizedRestriction id W
    intro A hA
    exact (Measure.measurable_coe (hA.measurableSet.inter hW)).div (Measure.measurable_coe hW)
  let U : Ω → {η : Measure ℂ // IsFiniteMeasure η} :=
    fun ω => ⟨normalizedRestriction (μ ω) W, inferInstance⟩
  let V : Ξ → {η : Measure ℂ // IsFiniteMeasure η} :=
    fun ω => ⟨normalizedRestriction (ν ω) W, inferInstance⟩
  have hU : Measurable U := (hnorm.comp hμ).subtype_mk
  have hV : Measurable V := (hnorm.comp hν).subtype_mk
  exact finiteMeasure_law_absolutelyContinuous_of_common_approximations P Q X Y hX hY hdom
    U V hU hV S hcount hgen hpi hsets huniv f hf hu hv

#print axioms finiteMeasure_law_absolutelyContinuous_of_common_approximations
#print axioms normalizedRestriction_law_absolutelyContinuous_of_common_approximations

end HarmonicBalls
