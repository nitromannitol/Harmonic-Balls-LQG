import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.FirstPass.S11aa

/-! # The LQG metric axioms on a sample space in `Type u` are derived (phase 2, worker z4)

Task fp-phase2-axioms-univ-derive. Derives `LQGMetricSatisfiesAxiomsUnivFrozen` (FirstPass/Frozen/S11g.lean:31) from the
Defs field `IsLQGMetric.satisfiesLQGMetricAxioms` (Defs/LQGMetric.lean:183), which quantifies over `Ω : Type` only.
Written route: notes/fp-gaps/CHATGPT-hb-distribution-frozen.md section 4, with one correction. Section 4.2 pushes the
whole circle process through a null-set modification; here only the circle component is modified off a measurable
null set `G0` (`circleOn`), and the pairing component is kept exactly as `hC ω`. Only the pairing enters the pairing
σ-algebras of the locality axiom II, so an exact pairing makes the locality measurability transfer exact.

Sample space. `UnivSample := CircleSample × ContShift` with `CircleSample` from `FirstPassS11aa` (pairing functional and
circle process continuous on `(0, ∞) × ℂ`) and `ContShift := {g // Continuous g}`. The sample map is
`ω ↦ ((hC ω, circleOn ω), f ω)`, measurable, and its field `addFunPairing (pairing) (shift)` equals
`addFunPairing (hC ω) (f ω)` for every `ω`.

Transfer. `P.map J` is a whole-plane GFF on `UnivSample` (the six clauses of `IsWholePlaneGFF` transfer as in
`FirstPassS11aa.isWholePlaneGFF_map_sample`), the axioms are applied with `Ω := UnivSample : Type`, and each clause is
pulled back along `J` by `ae_of_ae_map`. -/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal
open FirstPassS11aa

/-- Continuous shifts, as a Type-0 carrier. -/
abbrev ContShift : Type := {g : ℂ → ℝ // Continuous g}

/-- The Type-0 sample space of the transported model: pairing functional with circle process, and continuous shift. -/
abbrev UnivSample : Type := CircleSample × ContShift

/-- The circle process on `G0` (positive radii), and the zero process off `G0`. -/
noncomputable def circleOn {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω) (ω : Ω) : ℝ → ℂ → ℝ :=
  by
    classical
    exact if ω ∈ G0 then posCircle hcirc ω else fun _ _ => 0

lemma circleOn_continuousOn {Ω : Type*} {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) (ω : Ω) :
    ContinuousOn (fun q : ℝ × ℂ => circleOn hcirc G0 ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  unfold circleOn
  by_cases hω : ω ∈ G0
  · simp only [hω, ite_true]
    refine (hG0 ω hω).congr fun q hq => ?_
    simp [posCircle, show (0 : ℝ) < q.1 from hq.1]
  · simp only [hω, ite_false]
    exact continuousOn_const

/-- The circle component of the sample: `circleOn` at `ω`. -/
lemma measurable_circleOn {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0m : MeasurableSet G0) (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable (circleOn hcirc G0) := by
  unfold circleOn
  classical
  exact Measurable.ite hG0m (measurable_posCircle hcirc_meas) measurable_const

/-- The `CircleSample` of `ω`: the exact pairing `hC ω` and the circle process `circleOn ω`. -/
noncomputable def circleSample {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    (ω : Ω) : CircleSample :=
  ⟨(toPairingFun (hC ω), circleOn hcirc G0 ω), circleOn_continuousOn hG0 ω⟩

lemma measurable_circleSample {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hC_meas : ∀ φ, IsTestFunction (univ : Set ℂ) φ → Measurable fun ω => hC ω φ)
    (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) :
    Measurable (circleSample hC hcirc G0 hG0) :=
  ((measurable_toPairingFun hC_meas).prodMk (measurable_circleOn hG0m hcirc_meas)).subtype_mk

/-- On `G0`, the circle component agrees with the positive-radius process, so every admissible observable agrees. -/
lemma eval_circleSample_eq {Ω : Type*} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω} {ω : Ω}
    (hω : ω ∈ G0) (o : GFFObservable.Admissible) :
    o.1.eval (hC ω) (hcirc ω) = o.1.eval (hC ω) (circleOn hcirc G0 ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => simp [GFFObservable.eval]
  | circle r z =>
    have hr : 0 < r := ho
    simp [circleOn, hω, GFFObservable.eval, posCircle, hr]

/-- The sample map `Ω → UnivSample`, `ω ↦ (circleSample ω, f ω)`. -/
noncomputable def univSample {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (G0 : Set Ω)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) (ω : Ω) : UnivSample :=
  (circleSample hC hcirc G0 hG0 ω, ⟨f ω, hf ω⟩)

lemma measurable_univSample {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hC_meas : ∀ φ, IsTestFunction (univ : Set ℂ) φ → Measurable fun ω => hC ω φ)
    (hcirc_meas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hG0 : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x) :
    Measurable (univSample hC hcirc G0 hG0 f hf) :=
  (measurable_circleSample hG0m hC_meas hcirc_meas hG0).prodMk
    (measurable_pi_iff.2 hfm).subtype_mk

lemma measurable_pairX : Measurable fun x : UnivSample => x.1.1.1 :=
  measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)

lemma measurable_circX (r : ℝ) (z : ℂ) : Measurable fun x : UnivSample => x.1.1.2 r z :=
  (measurable_circleCoord r z).comp measurable_fst

lemma measurable_evalObsX (o : GFFObservable.Admissible) :
    Measurable fun x : UnivSample => o.1.eval x.1.1.1 x.1.1.2 :=
  (measurable_evalObs o).comp measurable_fst

lemma measurable_shiftX (z : ℂ) : Measurable fun x : UnivSample => x.2.1 z :=
  (measurable_pi_apply z).comp (measurable_subtype_coe.comp measurable_snd)

/-- The transported whole-plane GFF: `P.map (univSample)` is a whole-plane GFF on `UnivSample`, with pairing
`x ↦ x.1.1.1` and circle process `x ↦ x.1.1.2`. Mirrors `FirstPassS11aa.isWholePlaneGFF_map_sample`. -/
theorem isWholePlaneGFF_map_univSample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {G0 : Set Ω} (hG0m : MeasurableSet G0)
    (hG0 : ∀ᵐ ω ∂P, ω ∈ G0)
    (hG0c : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x) :
    IsWholePlaneGFF (P.map (univSample hC hcirc G0 hG0c f hf)) (fun x : UnivSample => x.1.1.1)
      (fun x : UnivSample => x.1.1.2) := by
  have hJm : Measurable (univSample hC hcirc G0 hG0c f hf) :=
    measurable_univSample hG0m hGFF.measurable_pairing hGFF.measurable_circle hG0c hf hfm
  refine
    { measurable_pairing := fun φ hφ => (measurable_evalPairing hφ).comp measurable_pairX
      measurable_circle := fun r z _ => measurable_circX r z
      isGaussianProcess := ⟨fun I => ?_⟩
      integral_eq_zero := fun o ho => ?_
      covariance_eq := fun o o' ho ho' => ?_
      ae_continuousOn_circle := Filter.Eventually.of_forall fun x => x.1.2 }
  · refine hasGaussianLaw_map_of_comp hJm ?_ ?_
    · refine Measurable.of_eval fun i => ?_
      exact measurable_evalObsX i.1
    · refine (hGFF.isGaussianProcess.hasGaussianLaw I).congr ?_
      filter_upwards [hG0] with ω hω
      funext i
      exact eval_circleSample_eq hω i.1
  · have hm : Measurable fun x : UnivSample => o.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o, ho⟩
    have hae : (fun ω => o.eval (univSample hC hcirc G0 hG0c f hf ω).1.1.1
        (univSample hC hcirc G0 hG0c f hf ω).1.1.2) =ᵐ[P] fun ω => o.eval (hC ω) (hcirc ω) := by
      filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o, ho⟩).symm
    exact ((integral_map_of_measurable hJm hm).trans (integral_congr_ae hae)).trans
      (hGFF.integral_eq_zero o ho)
  · have hm : Measurable fun x : UnivSample => o.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o, ho⟩
    have hm' : Measurable fun x : UnivSample => o'.eval x.1.1.1 x.1.1.2 := measurable_evalObsX ⟨o', ho'⟩
    refine (covariance_map_of_ae hJm hm hm' ?_ ?_).trans (hGFF.covariance_eq o o' ho ho')
    · filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o, ho⟩).symm
    · filter_upwards [hG0] with ω hω
      exact (eval_circleSample_eq hω ⟨o', ho'⟩).symm

/-- The sample map is measurable from the pairing σ-algebra of `addFunPairing (hC ω) (f ω)` over `U` into the pairing
σ-algebra of the sample field over `U`: the sample field is the sample pairing plus the sample shift, and its pairings
with test functions are the pairings of `addFunPairing (hC ω) (f ω)`, exactly. -/
lemma measurable_univSample_pairing {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {G0 : Set Ω}
    (hG0c : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {f : Ω → ℂ → ℝ} (hf : ∀ ω, Continuous (f ω)) (U : Set ℂ) :
    Measurable[pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (f ω)) U,
      pairingSigmaAlgebra (fun x : UnivSample => addFunPairing x.1.1.1 x.2.1) U]
      (univSample hC hcirc G0 hG0c f hf) := by
  refine measurable_iff_comap_le.2 ?_
  show MeasurableSpace.comap _ (pairingSigmaAlgebra (fun x : UnivSample => addFunPairing x.1.1.1 x.2.1) U) ≤ _
  unfold pairingSigmaAlgebra
  simp only [MeasurableSpace.comap_iSup]
  refine iSup₂_le fun φ hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ) =>
    MeasurableSpace.comap (fun ω => addFunPairing (hC ω) (f ω) ψ) inferInstance) φ hφ

/-- **Derived.** The LQG metric axioms I-IV hold for every whole-plane GFF `hC` with a random continuous shift `f` on a
sample space in an arbitrary universe, for every field `𝔇` with `IsLQGMetric γ ξ 𝔇`. Proved by transport to the
Type-0 sample space `UnivSample`, where the Defs field `IsLQGMetric.satisfiesLQGMetricAxioms` applies, and pullback of
each clause along `univSample` (the sample field is `addFunPairing (hC ω) (f ω)` exactly, so the pullbacks are exact,
and the almost sure clauses pull back by `ae_of_ae_map`). No new hypothesis. -/
theorem lqgMetricSatisfiesAxiomsUniv_derived : LQGMetricSatisfiesAxiomsUnivFrozen.{u} := by
  intro γ ξ 𝔇 hLQG Ω _ P hC hcirc f hGFF hf hfm
  obtain ⟨G0, hG0m, hG0, hG0c⟩ := exists_good_set hGFF.ae_continuousOn_circle
  have hGFF' := isWholePlaneGFF_map_univSample hGFF hG0m hG0 hG0c hf hfm
  have hJm : Measurable (univSample hC hcirc G0 hG0c f hf) :=
    measurable_univSample hG0m hGFF.measurable_pairing hGFF.measurable_circle hG0c hf hfm
  have hS := hLQG.satisfiesLQGMetricAxioms UnivSample (P.map (univSample hC hcirc G0 hG0c f hf))
    (fun x : UnivSample => x.1.1.1) (fun x : UnivSample => x.1.1.2) (fun x : UnivSample => x.2.1) hGFF'
    (fun x => x.2.2) (fun z => measurable_shiftX z)
  refine
    { ae_isEuclideanLengthMetric := ?_
      locality := ?_
      ae_weylScaling := ?_
      coordChange := ?_ }
  · exact ae_of_ae_map hJm.aemeasurable hS.ae_isEuclideanLengthMetric
  · intro U hU
    obtain ⟨G, hGm, hGeq⟩ := hS.locality U hU
    refine ⟨fun ω => G (univSample hC hcirc G0 hG0c f hf ω), fun z w => ?_, ?_⟩
    · exact (hGm z w).comp (measurable_univSample_pairing hG0c hf U)
    · exact ae_of_ae_map hJm.aemeasurable hGeq
  · exact ae_of_ae_map hJm.aemeasurable hS.ae_weylScaling
  · intro r hr z
    exact ae_of_ae_map hJm.aemeasurable (hS.coordChange r hr z)

end HarmonicBalls
