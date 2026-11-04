import HarmonicBalls.Proofs.Sec8.FiniteMeasureApproximationLaw

/-! # Joint observed-field and local mass laws

Common measurable mass approximations transfer the joint law of the
observation and its local measure, preserving any dependence on the root.
The Section 8 phase-frequency argument uses Leonardo Bonanno’s
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Common countable approximations transfer their joint law with the observed
field, not merely the marginal law of the limits. -/
theorem joint_countable_limit_law_absolutelyContinuous
    {E Ω Ξ ι : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Countable ι]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (f : ι → ℕ → E → ℝ) (hf : ∀ i n, Measurable (f i n))
    (u : ι → Ω → ℝ) (v : ι → Ξ → ℝ)
    (hu : ∀ i, TendstoInMeasure P (fun n ω => f i n (X ω)) atTop (u i))
    (hv : ∀ i, TendstoInMeasure Q (fun n ω => f i n (Y ω)) atTop (v i)) :
    Q.map (fun ω => (Y ω, fun i => v i ω)) ≪
      P.map (fun ω => (X ω, fun i => u i ω)) := by
  obtain ⟨F, hFm, hFP, hFQ⟩ :=
    exists_common_countable_limits_of_tendstoInMeasure P Q X Y f hf u v hu hv
  have hF : Measurable (fun x => (x, fun i => F i x)) :=
    measurable_id.prodMk (Measurable.of_eval hFm)
  have hP : P.map (fun ω => (X ω, fun i => u i ω)) =
      P.map ((fun x => (x, fun i => F i x)) ∘ X) := by
    apply Measure.map_congr
    filter_upwards [hFP] with ω hω
    congr 1
    funext i
    exact (hω i).symm
  have hQ : Q.map (fun ω => (Y ω, fun i => v i ω)) =
      Q.map ((fun x => (x, fun i => F i x)) ∘ Y) := by
    apply Measure.map_congr
    filter_upwards [hFQ] with ω hω
    congr 1
    funext i
    exact (hω i).symm
  rw [hQ, hP, ← Measure.map_map hF hY, ← Measure.map_map hF hX]
  exact hdom.map hF

/-- Common mass approximations transfer the joint law of the observation
and the entire finite measure. -/
theorem joint_finiteMeasure_law_absolutelyContinuous_of_common_approximations
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
    Q.map (fun ω => (Y ω, (V ω).val)) ≪ P.map (fun ω => (X ω, (U ω).val)) := by
  let : Countable S := hcount.to_subtype
  let L := {μ : Measure ℂ // IsFiniteMeasure μ}
  let encode : L → S → ℝ := fun μ A => (μ.val A.val).toReal
  have hencode : Measurable encode := by
    apply Measurable.of_eval
    intro A
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_coe (hsets A.val A.property)).comp measurable_subtype_coe)
  have hdom' : Q.map (fun ω => (Y ω, encode (V ω))) ≪
      P.map (fun ω => (X ω, encode (U ω))) := by
    exact joint_countable_limit_law_absolutelyContinuous P Q X Y hX hY hdom f hf
      (fun A ω => ((U ω).val A.val).toReal)
      (fun A ω => ((V ω).val A.val).toReal) hu hv
  let enc : E × L → E × (S → ℝ) := fun q => (q.1, encode q.2)
  let m : MeasurableSpace (E × L) := MeasurableSpace.comap enc inferInstance
  have hobs : @Measurable (E × L) E m _ Prod.fst := by
    let : MeasurableSpace (E × L) := m
    have hm : Measurable (fun q : E × (S → ℝ) => q.1) := measurable_fst
    exact hm.comp (comap_measurable enc)
  have hcoe : @Measurable (E × L) (Measure ℂ) m _ (fun q => q.2.val) := by
    let : MeasurableSpace (E × L) := m
    let (q : E × L) : IsFiniteMeasure q.2.val := q.2.property
    apply Measurable.measure_of_isPiSystem hgen hpi
    · intro A hA
      have hm : Measurable (fun q : E × L => ENNReal.ofReal (encode q.2 ⟨A, hA⟩)) :=
        ENNReal.measurable_ofReal.comp ((measurable_pi_apply (⟨A, hA⟩ : S)).comp
          (measurable_snd.comp (comap_measurable enc)))
      convert hm using 1
      funext q
      exact (ENNReal.ofReal_toReal (measure_ne_top q.2.val A)).symm
    · have hm : Measurable (fun q : E × L => ENNReal.ofReal (encode q.2 ⟨univ, huniv⟩)) :=
        ENNReal.measurable_ofReal.comp ((measurable_pi_apply (⟨univ, huniv⟩ : S)).comp
          (measurable_snd.comp (comap_measurable enc)))
      convert hm using 1
      funext q
      exact (ENNReal.ofReal_toReal (measure_ne_top q.2.val univ)).symm
  have hpair : @Measurable (E × L) (E × Measure ℂ) m _ (fun q => (q.1, q.2.val)) :=
    hobs.prodMk hcoe
  refine Measure.AbsolutelyContinuous.mk ?_
  intro A hA hz
  obtain ⟨B, hB, heq⟩ := MeasurableSpace.measurableSet_comap.mp (hpair hA)
  have hpreU : (fun ω => (X ω, encode (U ω))) ⁻¹' B =
      (fun ω => (X ω, (U ω).val)) ⁻¹' A := by
    ext ω
    exact Set.ext_iff.mp heq (X ω, U ω)
  have hpreV : (fun ω => (Y ω, encode (V ω))) ⁻¹' B =
      (fun ω => (Y ω, (V ω).val)) ⁻¹' A := by
    ext ω
    exact Set.ext_iff.mp heq (Y ω, V ω)
  have hXenc : Measurable (fun ω => (X ω, encode (U ω))) :=
    hX.prodMk (hencode.comp hU)
  have hYenc : Measurable (fun ω => (Y ω, encode (V ω))) :=
    hY.prodMk (hencode.comp hV)
  have hXval : Measurable (fun ω => (X ω, (U ω).val)) :=
    hX.prodMk (measurable_subtype_coe.comp hU)
  have hYval : Measurable (fun ω => (Y ω, (V ω).val)) :=
    hY.prodMk (measurable_subtype_coe.comp hV)
  have hz' : Q.map (fun ω => (Y ω, encode (V ω))) B = 0 := by
    apply hdom'
    rw [Measure.map_apply hXenc hB, hpreU,
      ← Measure.map_apply hXval hA]
    exact hz
  rwa [Measure.map_apply hYenc hB, hpreV,
    ← Measure.map_apply hYval hA] at hz'

/-- Shared approximations transfer the joint law of the observation and
normalized restriction, retaining their dependence. -/
theorem joint_normalizedRestriction_law_absolutelyContinuous_of_common_approximations
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
    Q.map (fun ω => (Y ω, normalizedRestriction (ν ω) W)) ≪
      P.map (fun ω => (X ω, normalizedRestriction (μ ω) W)) := by
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
  exact joint_finiteMeasure_law_absolutelyContinuous_of_common_approximations P Q X Y hX hY hdom
    U V hU hV S hcount hgen hpi hsets huniv f hf hu hv

#print axioms joint_normalizedRestriction_law_absolutelyContinuous_of_common_approximations

#print axioms joint_finiteMeasure_law_absolutelyContinuous_of_common_approximations

#print axioms joint_countable_limit_law_absolutelyContinuous

end HarmonicBalls
