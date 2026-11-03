import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-!
# A mixture of whole-plane GFFs is a whole-plane GFF

Proof of `WholePlaneGFFMixtureStep` (HarmonicBalls/Steps/Sec2/VolumeGrowth.lean). `IsWholePlaneGFF` determines
every finite-dimensional law of the admissible observables: it is Gaussian with mean `0` and covariance
`wholePlaneGFFCov` (`IsWholePlaneGFF.map_restrict_eq`, from Mathlib's `IsGaussian.ext_covarianceBilinDual`).
Hence, for fields `(hC k, hcirc k)`, `k ∈ ℕ`, each a whole-plane GFF under `P`, the field `(k, ω) ↦ (hC k ω,
hcirc k ω)` under `ν ⊗ P` has the same finite-dimensional laws (`map_mixture_eq`), and is again a whole-plane GFF.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u

/-- The covariance of two continuous linear functionals of a random vector in `ι → ℝ`, through the
coordinates. -/
theorem covariance_strongDual_comp {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    [Fintype ι]
    [DecidableEq ι] {X : Ω → ι → ℝ} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) (L₁ L₂ : StrongDual ℝ (ι → ℝ)) :
    cov[fun ω => L₁ (X ω), fun ω => L₂ (X ω); P] =
      ∑ i, ∑ j, L₁ (fun k => if i = k then 1 else 0) * L₂ (fun k => if j = k then 1 else 0) *
        cov[fun ω => X ω i, fun ω => X ω j; P] := by
  have hL : ∀ L : StrongDual ℝ (ι → ℝ), ∀ x : ι → ℝ,
      L x = ∑ i, L (fun k => if i = k then 1 else 0) * x i := by
    intro L x
    have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h1 : (fun ω => L₁ (X ω)) = fun ω => ∑ i, L₁ (fun k => if i = k then 1 else 0) * X ω i :=
    funext fun ω => hL L₁ (X ω)
  have h2 : (fun ω => L₂ (X ω)) = fun ω => ∑ i, L₂ (fun k => if i = k then 1 else 0) * X ω i :=
    funext fun ω => hL L₂ (X ω)
  rw [h1, h2]
  rw [covariance_fun_sum_left (X := fun i ω => L₁ (fun k => if i = k then 1 else 0) * X ω i)
    (fun i => (hX i).const_mul _) (memLp_finsetSum _ fun j _ => (hX j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [covariance_const_mul_left, covariance_fun_sum_right
    (X := fun j ω => L₂ (fun k => if j = k then 1 else 0) * X ω j) (fun j => (hX j).const_mul _) (hX i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_right]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The vector of the observables in a finite set `I` of admissible observables. -/
def obsVector (I : Finset GFFObservable.Admissible) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) :
    I → ℝ :=
  I.restrict fun o : GFFObservable.Admissible => o.1.eval hC hcirc

/-- `IsWholePlaneGFF` determines the finite-dimensional laws. -/
theorem IsWholePlaneGFF.map_restrict_eq {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc')
    (I : Finset GFFObservable.Admissible) :
    P.map (fun ω => obsVector I (hC ω) (hcirc ω)) = P.map (fun ω => obsVector I (hC' ω) (hcirc' ω)) := by
  classical
  have hP := h.isProbabilityMeasure
  have hG : HasGaussianLaw (fun ω => obsVector I (hC ω) (hcirc ω)) P :=
    h.isGaussianProcess.hasGaussianLaw I
  have hG' : HasGaussianLaw (fun ω => obsVector I (hC' ω) (hcirc' ω)) P :=
    h'.isGaussianProcess.hasGaussianLaw I
  have := hG.isGaussian_map
  have := hG'.isGaussian_map
  have hc : ∀ i : I, HasGaussianLaw (fun ω => obsVector I (hC ω) (hcirc ω) i) P := fun i =>
    h.isGaussianProcess.hasGaussianLaw_eval i.1
  have hc' : ∀ i : I, HasGaussianLaw (fun ω => obsVector I (hC' ω) (hcirc' ω) i) P := fun i =>
    h'.isGaussianProcess.hasGaussianLaw_eval i.1
  have hmean : ∀ {Y : Ω → I → ℝ}, AEMeasurable Y P → (∀ i, Integrable (fun ω => Y ω i) P) →
      (∀ i, ∫ ω, Y ω i ∂P = 0) → (P.map Y)[id] = 0 := by
    intro Y hY hint h0
    rw [integral_map hY aestronglyMeasurable_id]
    simp only [id_eq]
    funext i
    rw [eval_integral hint]
    exact h0 i
  apply IsGaussian.ext_covarianceBilinDual
  · rw [hmean hG.aemeasurable (fun i => (hc i).integrable) (fun i => h.integral_eq_zero i.1.1 i.1.2),
      hmean hG'.aemeasurable (fun i => (hc' i).integrable) (fun i => h'.integral_eq_zero i.1.1 i.1.2)]
  · ext L₁ L₂
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id,
      covariance_map (by fun_prop) (by fun_prop) hG.aemeasurable,
      covariance_map (by fun_prop) (by fun_prop) hG'.aemeasurable]
    simp only [Function.comp_def]
    rw [covariance_strongDual_comp (fun i => (hc i).memLp_two),
      covariance_strongDual_comp (fun i => (hc' i).memLp_two)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e1 := h.covariance_eq i.1.1 j.1.1 i.1.2 j.1.2
    have e2 := h'.covariance_eq i.1.1 j.1.1 i.1.2 j.1.2
    congr 1
    exact e1.trans e2.symm

/-- The law of a mixture of random variables with a common law. -/
theorem map_mixture_eq {E : Type*} [MeasurableSpace E] [SFinite P] {ν : Measure ℕ} [IsProbabilityMeasure ν]
    {Y : ℕ → Ω → E} (hY : ∀ k, Measurable (Y k)) (hlaw : ∀ k, P.map (Y k) = P.map (Y 0)) :
    (ν.prod P).map (fun x => Y x.1 x.2) = P.map (Y 0) := by
  have hmeas : Measurable (fun x : ℕ × Ω => Y x.1 x.2) := measurable_from_prod_countable_right hY
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.prod_apply (hmeas hA)]
  have h : ∀ k, P (Prod.mk k ⁻¹' ((fun x : ℕ × Ω => Y x.1 x.2) ⁻¹' A)) = P.map (Y 0) A := by
    intro k
    rw [← hlaw k, Measure.map_apply (hY k) hA]; rfl
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one]

/-- Almost sure statements for every slice hold for the mixture under `ν ⊗ P`. -/
theorem ae_prod_nat_of_forall [SFinite P] {ν : Measure ℕ} {p : ℕ → Ω → Prop}
    (h : ∀ k, ∀ᵐ ω ∂P, p k ω) : ∀ᵐ x ∂(ν.prod P), p x.1 x.2 := by
  rw [ae_iff]
  set N : ℕ → Set Ω := fun k => toMeasurable P {ω | ¬ p k ω}
  have hN : ∀ k, P (N k) = 0 := fun k => by rw [measure_toMeasurable]; exact ae_iff.1 (h k)
  refine measure_mono_null (t := ⋃ k, ({k} : Set ℕ) ×ˢ N k) ?_ (measure_iUnion_null fun k => ?_)
  · rintro ⟨k, ω⟩ hx
    exact mem_iUnion.2 ⟨k, mem_singleton k, subset_toMeasurable P _ hx⟩
  · rw [Measure.prod_prod, hN, mul_zero]

/-- `WholePlaneGFFMixtureStep`: a mixture of whole-plane GFFs is a whole-plane GFF. -/
theorem wholePlaneGFFMixtureStep_holds : WholePlaneGFFMixtureStep.{u} := by
  intro Ω _ P hC hcirc ν hν hG
  have hP := (hG 0).isProbabilityMeasure
  have hmeasO : ∀ k (o : GFFObservable.Admissible), Measurable fun ω => o.1.eval (hC k ω) (hcirc k ω) := by
    rintro k ⟨o, ho⟩
    cases o with
    | pairing φ => exact (hG k).measurable_pairing φ ho
    | circle r z => exact (hG k).measurable_circle r z ho
  have hmeasI : ∀ k (I : Finset GFFObservable.Admissible),
      Measurable fun ω => obsVector I (hC k ω) (hcirc k ω) := fun k I =>
    measurable_pi_iff.2 fun i => hmeasO k i.1
  have hlawI : ∀ I : Finset GFFObservable.Admissible,
      (ν.prod P).map (fun x => obsVector I (hC x.1 x.2) (hcirc x.1 x.2)) =
        P.map (fun ω => obsVector I (hC 0 ω) (hcirc 0 ω)) := fun I =>
    map_mixture_eq (Y := fun k ω => obsVector I (hC k ω) (hcirc k ω)) (fun k => hmeasI k I)
      (fun k => (hG k).map_restrict_eq (hG 0) I)
  have hmeasM : ∀ I : Finset GFFObservable.Admissible,
      Measurable fun x : ℕ × Ω => obsVector I (hC x.1 x.2) (hcirc x.1 x.2) := fun I =>
    measurable_from_prod_countable_right fun k => hmeasI k I
  refine ⟨fun φ hφ => ?_, fun r z hr => ?_, ⟨fun I => ?_⟩, fun o ho => ?_, fun o o' ho ho' => ?_, ?_⟩
  · exact measurable_from_prod_countable_right fun k => (hG k).measurable_pairing φ hφ
  · exact measurable_from_prod_countable_right fun k => (hG k).measurable_circle r z hr
  · refine ⟨(hmeasM I).aemeasurable, ?_⟩
    have h := hlawI I
    simp only [obsVector] at h
    rw [h]
    exact ((hG 0).isGaussianProcess.hasGaussianLaw I).isGaussian_map
  · classical
    set I : Finset GFFObservable.Admissible := {⟨o, ho⟩}
    set i : I := ⟨⟨o, ho⟩, Finset.mem_singleton_self _⟩
    have hg : Measurable fun v : I → ℝ => v i := measurable_pi_apply i
    have h1 := integral_map (μ := ν.prod P) (hmeasM I).aemeasurable hg.aestronglyMeasurable
    have h2 := integral_map (μ := P) (hmeasI 0 I).aemeasurable hg.aestronglyMeasurable
    rw [hlawI I] at h1
    exact h1.symm.trans (h2.trans ((hG 0).integral_eq_zero o ho))
  · classical
    set I : Finset GFFObservable.Admissible := {⟨o, ho⟩, ⟨o', ho'⟩}
    set i : I := ⟨⟨o, ho⟩, Finset.mem_insert_self _ _⟩
    set j : I := ⟨⟨o', ho'⟩, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    have hgi : Measurable fun v : I → ℝ => v i := measurable_pi_apply i
    have hgj : Measurable fun v : I → ℝ => v j := measurable_pi_apply j
    have h1 := covariance_map (μ := ν.prod P) hgi.aestronglyMeasurable hgj.aestronglyMeasurable
      (hmeasM I).aemeasurable
    have h2 := covariance_map (μ := P) hgi.aestronglyMeasurable hgj.aestronglyMeasurable
      (hmeasI 0 I).aemeasurable
    rw [hlawI I] at h1
    exact h1.symm.trans (h2.trans ((hG 0).covariance_eq o o' ho ho'))
  · exact ae_prod_nat_of_forall (p := fun k ω => ContinuousOn (fun p : ℝ × ℂ => hcirc k ω p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ)) fun k => (hG k).ae_continuousOn_circle

end HarmonicBalls
