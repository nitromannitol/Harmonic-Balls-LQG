import HarmonicBalls.FirstPass.S11i.CanonicalLawUniversal

/-! # Observable laws and the two-copy mixture of whole-plane GFF models

* `observable_map_eq`: two whole-plane GFF models (on possibly different spaces) have the same law of the vector of
  their admissible observables (pairings with test functions and circle averages). Proof as in
  `canonicalLaw_eq_of_isWholePlaneGFF` (`FirstPass/S11i/CanonicalLawUniversal.lean`): cylinder sets and Gaussian vectors
  with equal centred covariance (`map_eq_of_gaussian_cov_two`).
* `isWholePlaneGFF_of_observable_map`: a model whose observable law equals that of a GFF model is a GFF model, given the
  measurability of pairings and circle averages and the a.s. continuity of the circle averages.
* `mixMeasure P P' = ½ P.map inl + ½ P'.map inr` on `Ω ⊕ Ω`; `isWholePlaneGFF_mixMeasure`: the combined model of two
  GFF models is a GFF model; `ae_mix_iff`: almost sure properties of the mixture are those of the two branches.
No input is used beyond `IsWholePlaneGFF` and Mathlib.
-/

namespace HarmonicBalls.S11aj

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-- An admissible observable is measurable in the sample, given the measurability of pairings and circle averages. -/
theorem measurable_obs_of {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hpair : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC ω φ)
    (hcirc_m : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) (o : GFFObservable.Admissible) :
    Measurable fun ω => o.1.eval (hC ω) (hcirc ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact hpair φ ho
  | circle r z => exact hcirc_m r z ho

/-- The observable law of a whole-plane GFF model: the vector of its admissible observables. Two GFF models have the
same observable law. -/
theorem observable_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') :
    P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) =
      P'.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) := by
  have hm : Measurable (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) :=
    measurable_pi_iff.2 fun o => measurable_obs_of hh.measurable_pairing hh.measurable_circle o
  have hm' : Measurable (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC' ω) (hcirc' ω)) :=
    measurable_pi_iff.2 fun o => measurable_obs_of hh'.measurable_pairing hh'.measurable_circle o
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : GFFObservable.Admissible => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    simp only [measurableCylinders, mem_iUnion, mem_singleton_iff, exists_prop] at hs
    obtain ⟨J, B, hB, rfl⟩ := hs
    have hg : Measurable (fun (f : GFFObservable.Admissible → ℝ) (i : J) => f i.1) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.1
    have hcyl : MeasurableSet (cylinder J B) := hg hB
    have hY0 : Measurable (fun ω (j : J) => j.1.1.eval (hC ω) (hcirc ω)) :=
      measurable_pi_iff.2 fun j => measurable_obs_of hh.measurable_pairing hh.measurable_circle j.1
    have hY0' : Measurable (fun ω (j : J) => j.1.1.eval (hC' ω) (hcirc' ω)) :=
      measurable_pi_iff.2 fun j => measurable_obs_of hh'.measurable_pairing hh'.measurable_circle j.1
    have hJ := map_eq_of_gaussian_cov_two (ι := J)
      (Y := fun (j : J) ω => j.1.1.eval (hC ω) (hcirc ω))
      (Y' := fun (j : J) ω => j.1.1.eval (hC' ω) (hcirc' ω))
      (fun j => measurable_obs_of hh.measurable_pairing hh.measurable_circle j.1)
      (fun j => measurable_obs_of hh'.measurable_pairing hh'.measurable_circle j.1)
      (hh.isGaussianProcess.hasGaussianLaw J) (hh'.isGaussianProcess.hasGaussianLaw J)
      (fun j => hh.integral_eq_zero j.1.1 j.1.2) (fun j => hh'.integral_eq_zero j.1.1 j.1.2)
      (fun j l => (hh.covariance_eq j.1.1 l.1.1 j.1.2 l.1.2).trans
        (hh'.covariance_eq j.1.1 l.1.1 j.1.2 l.1.2).symm)
    rw [Measure.map_apply hm hcyl, Measure.map_apply hm' hcyl]
    show P ((fun ω (j : J) => j.1.1.eval (hC ω) (hcirc ω)) ⁻¹' B) =
      P' ((fun ω (j : J) => j.1.1.eval (hC' ω) (hcirc' ω)) ⁻¹' B)
    rw [← Measure.map_apply hY0 hB, ← Measure.map_apply hY0' hB, hJ]
  · simp

/-- A Gaussian law transfers along an equality of image laws. -/
theorem hasGaussianLaw_of_map_eq {Ω Ω2 E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω2]
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [MeasurableSpace E] {P : Measure Ω} {P2 : Measure Ω2}
    {X : Ω → E} {X2 : Ω2 → E} (hX : HasGaussianLaw X P) (hX2 : Measurable X2) (h : P2.map X2 = P.map X) :
    HasGaussianLaw X2 P2 :=
  { aemeasurable := hX2.aemeasurable
    isGaussian_map := by rw [h]; exact hX.isGaussian_map }

/-- A model whose observable law is that of a whole-plane GFF model is a whole-plane GFF model, given the measurability
of pairings and circle averages and the a.s. continuity of the circle averages. -/
theorem isWholePlaneGFF_of_observable_map {Ω Ω2 : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω2] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {P2 : Measure Ω2} [IsProbabilityMeasure P2] {hC2 : Ω2 → (ℂ → ℝ) → ℝ} {hcirc2 : Ω2 → ℝ → ℂ → ℝ}
    (hlaw : P2.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC2 ω) (hcirc2 ω)) =
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)))
    (hpair : ∀ φ, IsTestFunction Set.univ φ → Measurable fun ω => hC2 ω φ)
    (hcirc_m : ∀ r z, 0 < r → Measurable fun ω => hcirc2 ω r z)
    (hcont : ∀ᵐ ω ∂P2, ContinuousOn (fun p : ℝ × ℂ => hcirc2 ω p.1 p.2) (Ioi 0 ×ˢ univ)) :
    IsWholePlaneGFF P2 hC2 hcirc2 := by
  have hZ : Measurable (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC2 ω) (hcirc2 ω)) :=
    measurable_pi_iff.2 fun o => measurable_obs_of hpair hcirc_m o
  have hZ0 : Measurable (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) :=
    measurable_pi_iff.2 fun o => measurable_obs_of hh.measurable_pairing hh.measurable_circle o
  have hcoord : ∀ a : GFFObservable.Admissible, Measurable fun y : GFFObservable.Admissible → ℝ => y a :=
    fun a => measurable_pi_apply a
  refine
    { measurable_pairing := hpair
      measurable_circle := hcirc_m
      isGaussianProcess := ⟨fun I => ?_⟩
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := hcont }
  · exact hasGaussianLaw_of_map_eq (hh.isGaussianProcess.hasGaussianLaw I)
      (measurable_pi_iff.2 fun i => measurable_obs_of hpair hcirc_m i.1)
      (by
        have h1 := congrArg (fun μ => μ.map (fun (y : GFFObservable.Admissible → ℝ) (i : I) => y i.1)) hlaw
        simp only [Measure.map_map (measurable_pi_iff.2 fun (i : I) => measurable_pi_apply i.1) hZ,
          Measure.map_map (measurable_pi_iff.2 fun (i : I) => measurable_pi_apply i.1) hZ0] at h1
        exact h1)
  · intro o ho
    rw [show (∫ ω, o.eval (hC2 ω) (hcirc2 ω) ∂P2) =
        ∫ y, y ⟨o, ho⟩ ∂(P2.map fun ω (a : GFFObservable.Admissible) => a.1.eval (hC2 ω) (hcirc2 ω)) from
        (integral_map hZ.aemeasurable (hcoord ⟨o, ho⟩).aestronglyMeasurable).symm, hlaw,
      integral_map hZ0.aemeasurable (hcoord ⟨o, ho⟩).aestronglyMeasurable]
    exact hh.integral_eq_zero o ho
  · intro o o' ho ho'
    have c2 := covariance_map (μ := P2) (Z := fun ω (a : GFFObservable.Admissible) => a.1.eval (hC2 ω) (hcirc2 ω))
      (X := fun y : GFFObservable.Admissible → ℝ => y ⟨o, ho⟩) (Y := fun y => y ⟨o', ho'⟩)
      (hcoord _).aestronglyMeasurable (hcoord _).aestronglyMeasurable hZ.aemeasurable
    have c0 := covariance_map (μ := P) (Z := fun ω (a : GFFObservable.Admissible) => a.1.eval (hC ω) (hcirc ω))
      (X := fun y : GFFObservable.Admissible → ℝ => y ⟨o, ho⟩) (Y := fun y => y ⟨o', ho'⟩)
      (hcoord _).aestronglyMeasurable (hcoord _).aestronglyMeasurable hZ0.aemeasurable
    calc cov[fun ω => o.eval (hC2 ω) (hcirc2 ω), fun ω => o'.eval (hC2 ω) (hcirc2 ω); P2]
        = cov[fun y : GFFObservable.Admissible → ℝ => y ⟨o, ho⟩, fun y => y ⟨o', ho'⟩;
            P2.map fun ω (a : GFFObservable.Admissible) => a.1.eval (hC2 ω) (hcirc2 ω)] := c2.symm
      _ = cov[fun y : GFFObservable.Admissible → ℝ => y ⟨o, ho⟩, fun y => y ⟨o', ho'⟩;
            P.map fun ω (a : GFFObservable.Admissible) => a.1.eval (hC ω) (hcirc ω)] := by rw [hlaw]
      _ = cov[fun ω => o.eval (hC ω) (hcirc ω), fun ω => o'.eval (hC ω) (hcirc ω); P] := c0
      _ = wholePlaneGFFCov o o' := hh.covariance_eq o o' ho ho'

/-- The two-copy mixture `½ P.map inl + ½ P'.map inr` on the disjoint union `Ω ⊕ Ω`. -/
noncomputable def mixMeasure {Ω : Type*} [MeasurableSpace Ω] (P P' : Measure Ω) : Measure (Ω ⊕ Ω) :=
  (2⁻¹ : ℝ≥0∞) • P.map Sum.inl + (2⁻¹ : ℝ≥0∞) • P'.map Sum.inr

theorem isProbabilityMeasure_mixMeasure {Ω : Type*} [MeasurableSpace Ω] (P P' : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] : IsProbabilityMeasure (mixMeasure P P') := by
  constructor
  simp only [mixMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ, Measure.map_apply measurable_inr MeasurableSet.univ,
    preimage_univ, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Almost sure properties of the mixture are the almost sure properties of the two branches. -/
theorem ae_mix_iff {Ω : Type*} [MeasurableSpace Ω] {P P' : Measure Ω} (p : Ω ⊕ Ω → Prop) :
    (∀ᵐ x ∂mixMeasure P P', p x) ↔ (∀ᵐ ω ∂P, p (Sum.inl ω)) ∧ (∀ᵐ ω ∂P', p (Sum.inr ω)) := by
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := by simp
  have eI : MeasurableEmbedding (Sum.inl : Ω → Ω ⊕ Ω) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have eR : MeasurableEmbedding (Sum.inr : Ω → Ω ⊕ Ω) :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  rw [mixMeasure, ae_add_measure_iff, Measure.ae_ennreal_smul_measure_iff h2, Measure.ae_ennreal_smul_measure_iff h2, eI.ae_map_iff, eR.ae_map_iff]

/-- The combined model of two whole-plane GFF models is a whole-plane GFF model, with the mixture measure. -/
theorem isWholePlaneGFF_mixMeasure {Ω : Type*} [MeasurableSpace Ω] {P P' : Measure Ω} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hCs : Ω → (ℂ → ℝ) → ℝ}
    {hcirc_s : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hCs hcirc_s) :
    IsWholePlaneGFF (mixMeasure P P') (Sum.elim hC hCs) (Sum.elim hcirc hcirc_s) := by
  have := isProbabilityMeasure_mixMeasure P P'
  have hpair : ∀ φ, IsTestFunction Set.univ φ → Measurable fun x => Sum.elim hC hCs x φ := by
    intro φ hφ
    have e : (fun x => Sum.elim hC hCs x φ) =
        Sum.elim (fun ω => hC ω φ) (fun ω => hCs ω φ) := by
      funext x; cases x <;> rfl
    rw [e]
    exact Measurable.sumElim (hh.measurable_pairing φ hφ) (hh'.measurable_pairing φ hφ)
  have hcirc_m : ∀ r z, 0 < r → Measurable fun x => Sum.elim hcirc hcirc_s x r z := by
    intro r z hr
    have e : (fun x => Sum.elim hcirc hcirc_s x r z) =
        Sum.elim (fun ω => hcirc ω r z) (fun ω => hcirc_s ω r z) := by
      funext x; cases x <;> rfl
    rw [e]
    exact Measurable.sumElim (hh.measurable_circle r z hr) (hh'.measurable_circle r z hr)
  have hcont : ∀ᵐ x ∂mixMeasure P P',
      ContinuousOn (fun p : ℝ × ℂ => Sum.elim hcirc hcirc_s x p.1 p.2) (Ioi 0 ×ˢ univ) := by
    rw [ae_mix_iff]
    exact ⟨hh.ae_continuousOn_circle, hh'.ae_continuousOn_circle⟩
  have hZc : Measurable fun x (o : GFFObservable.Admissible) =>
      o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x) :=
    measurable_pi_iff.2 fun o => measurable_obs_of hpair hcirc_m o
  have hlaw : (mixMeasure P P').map (fun x (o : GFFObservable.Admissible) =>
      o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) =
      P.map (fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω)) := by
    have hZ' := observable_map_eq hh hh'
    unfold mixMeasure
    rw [Measure.map_add _ _ hZc, Measure.map_smul _ hZc.aemeasurable, Measure.map_smul _ hZc.aemeasurable,
      Measure.map_map hZc measurable_inl, Measure.map_map hZc measurable_inr]
    have e1 : (fun x (o : GFFObservable.Admissible) => o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) ∘
        Sum.inl = fun ω (o : GFFObservable.Admissible) => o.1.eval (hC ω) (hcirc ω) := rfl
    have e2 : (fun x (o : GFFObservable.Admissible) => o.1.eval (Sum.elim hC hCs x) (Sum.elim hcirc hcirc_s x)) ∘
        Sum.inr = fun ω (o : GFFObservable.Admissible) => o.1.eval (hCs ω) (hcirc_s ω) := rfl
    rw [e1, e2, hZ', ← add_smul, ENNReal.inv_two_add_inv_two, one_smul]
  exact isWholePlaneGFF_of_observable_map hh hlaw hpair hcirc_m hcont

end HarmonicBalls.S11aj
