import HarmonicBalls.FirstPass.Phase2.DMSFiniteTiltPosDerived
import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos

/-!
# The positive-radius joint marked identity from the finite-family tilt identity (MQ-lh-30 (a))

`dMSJointPos_of_finiteTiltPos` derives `DMSLemmaA10WholePlaneMarkedJointPosStmt`
(FirstPass/Phase2/RootedDominationJointPos.lean:64) from `DMSFiniteTiltPosStmt`
(FirstPass/Phase2/RootedDominationJointPosDerived.lean:28). Route: notes/fp-gaps/MATH-ANSWERS.md, section MQ-lh-30,
LEAN PLAN (a), steps J1-J7. The observation space is `PosObs = pairing × positive-radius profile × mark`, with the
σ-algebra `posObsSigma` (pairing σ-algebra tensor product σ-algebra). The two observation maps `obsG` (the field at the
mark, Duplantier-Miller-Sheffield Lemma A.10, left side) and `obsGs` (the DMS-shifted field at the mark, right side)
induce the two measures `leftMeas` and `rightMeas`; their agreement on cylinders gives the identity for every
measurable test (π-λ, `ext_of_generate_finite`).

This file holds J4 (measurability of the observation maps), J5 (the kernels and measures, their measurability) and
J7 step 1 (the finite-mass version `μ ↦ finRestr (Dec ∘ F)` of the LQG measure restricted to `B₁`).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

namespace DMSJointPosOfFinite

/-- The observation space of the positive-radius marked identity (plan J1): the pairing, the positive-radius circle
profile, and the mark. -/
abbrev PosObs : Type := ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ

/-- The σ-algebra of `PosObs`: the pairing σ-algebra on the first factor and the product σ-algebra on the profile and
the mark. It is the σ-algebra of `DMSLemmaA10WholePlaneMarkedJointPosStmt`. -/
noncomputable abbrev posObsSigma : MeasurableSpace PosObs :=
  (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance

attribute [local instance] posObsSigma

/-- The observation `G (ω, z)` of the field at the mark `z` (plan J4): the pairing and the positive-radius circle
profile of `ω`, with the mark `z`. -/
noncomputable def obsG {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (q : Ω × ℂ) : PosObs :=
  (hC q.1, fun p : CircleParameter => hcirc q.1 p.1 p.2, q.2)

/-- The DMS-shifted observation `Gs (z, ω)` (plan J4): the shifted pairing and the shifted positive-radius circle
profile of `ω` at the shift `z`, with the mark `z`. -/
noncomputable def obsGs {Ω : Type*} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (q : ℂ × Ω) :
    PosObs :=
  (dmsShiftedPairing γ q.1 (hC q.2) (hcirc q.2 1 0),
    fun p : CircleParameter => dmsShiftedCircle γ q.1 (hcirc q.2) p.1 p.2, q.1)

/-- **J4, the field observation is measurable.** -/
theorem measurable_obsG {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) : Measurable (obsG hC hcirc) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ measurable_snd)
  · exact (FirstPassS11atProducers.measurable_into_pairing hC fun φ hφ => hW.measurable_pairing φ hφ).comp
      measurable_fst
  · refine measurable_pi_iff.2 fun p => ?_
    exact (hW.measurable_circle p.1 p.2 p.1.2).comp measurable_fst

/-- **J4, the DMS-shifted observation is measurable.** The first factor is the pairing-level measurability of
`FirstPassS11atProducers.measurable_dmsShiftedPairing`; the profile is the coordinatewise sum of the three terms of
`dmsShiftedCircle`, as in `DMSFiniteTiltPosDerived` (lines 299-313). -/
theorem measurable_obsGs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) : Measurable (obsGs γ hC hcirc) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ measurable_fst)
  · exact FirstPassS11atProducers.measurable_dmsShiftedPairing P γ hC hcirc hW
  · refine measurable_pi_iff.2 fun p => ?_
    have h1 : Measurable (fun q : ℂ × Ω => hcirc q.2 p.1 p.2) :=
      (hW.measurable_circle p.1 p.2 p.1.2).comp measurable_snd
    have h2 : Measurable (fun q : ℂ × Ω => Real.circleAverage (dmsShift γ q.1) p.2 p.1) :=
      (measurable_circleAverage_dmsShift_centre γ p.2 p.1).comp measurable_fst
    have h3 : Measurable (fun q : ℂ × Ω => dmsConstant γ q.1 (hcirc q.2 1 0)) :=
      FirstPassS11atProducers.measurable_dmsConstant_joint γ (fun ω => hcirc ω 1 0)
        (hW.measurable_circle 1 0 one_pos)
    exact (h1.add h2).add h3

/-- The kernel `ω ↦ (ρ ω).map (G (ω, ·))` of plan J5. -/
noncomputable def leftKernel {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ρ : Ω → Measure ℂ)
    (ω : Ω) : Measure PosObs :=
  (ρ ω).map fun z => obsG hC hcirc (ω, z)

/-- The kernel `z ↦ P.map (Gs (z, ·))` of plan J5. -/
noncomputable def rightKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) : Measure PosObs :=
  P.map fun ω => obsGs γ hC hcirc (z, ω)

/-- The left measure `L := P.bind (ω ↦ (ρ ω).map (G (ω, ·)))` of plan J5. -/
noncomputable def leftMeas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ρ : Ω → Measure ℂ) : Measure PosObs :=
  P.bind (leftKernel hC hcirc ρ)

/-- The right measure `R := (volume.restrict B₁).bind (z ↦ P.map (Gs (z, ·)))` of plan J5. -/
noncomputable def rightMeas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Measure PosObs :=
  (volume.restrict (ball (0 : ℂ) 1)).bind (rightKernel P γ hC hcirc)

/-- **J5, the left kernel is measurable** (`Measure.measurable_of_measurable_coe`; the mass of a measurable set is a
finite-family lintegral, `DMSFiniteTiltPosDerived.measurable_lintegral_finite_family`). -/
theorem measurable_leftKernel {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {ρ : Ω → Measure ℂ} (hρ : Measurable ρ) (hfin : ∀ ω, IsFiniteMeasure (ρ ω))
    (hG : Measurable (obsG hC hcirc)) : Measurable (leftKernel hC hcirc ρ) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hA : MeasurableSet (obsG hC hcirc ⁻¹' S) := hG hS
  have hsl : ∀ ω, leftKernel hC hcirc ρ ω S
      = ∫⁻ z, (obsG hC hcirc ⁻¹' S).indicator (1 : Ω × ℂ → ℝ≥0∞) (ω, z) ∂(ρ ω) := by
    intro ω
    have hm : Measurable fun z => obsG hC hcirc (ω, z) := hG.comp measurable_prodMk_left
    have hs : MeasurableSet ((fun z => obsG hC hcirc (ω, z)) ⁻¹' S) := hm hS
    rw [leftKernel, Measure.map_apply hm hS, ← lintegral_indicator_one hs]
    refine lintegral_congr fun z => ?_
    rfl
  have hfun : (fun ω => leftKernel hC hcirc ρ ω S)
      = fun ω => ∫⁻ z, (obsG hC hcirc ⁻¹' S).indicator (1 : Ω × ℂ → ℝ≥0∞) (ω, z) ∂(ρ ω) :=
    funext hsl
  rw [hfun]
  exact DMSFiniteTiltPosDerived.measurable_lintegral_finite_family ρ hρ hfin
    (measurable_one.indicator hA)

/-- **J5, the right kernel is measurable** (`Measure.measurable_measure_prodMk_left`). -/
theorem measurable_rightKernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGs : Measurable (obsGs γ hC hcirc)) :
    Measurable (rightKernel P γ hC hcirc) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hfun : (fun z => rightKernel P γ hC hcirc z S)
      = fun z => P (Prod.mk z ⁻¹' (obsGs γ hC hcirc ⁻¹' S)) := by
    funext z
    have hm : Measurable fun ω => obsGs γ hC hcirc (z, ω) := hGs.comp measurable_prodMk_left
    rw [rightKernel, Measure.map_apply hm hS]
    rfl
  rw [hfun]
  exact measurable_measure_prodMk_left (hGs hS)

/-- The left measure evaluated on a measurable set (`Measure.bind_apply`). -/
theorem leftMeas_apply {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ρ : Ω → Measure ℂ) (hk : Measurable (leftKernel hC hcirc ρ))
    {S : Set PosObs} (hS : MeasurableSet S) :
    leftMeas P hC hcirc ρ S = ∫⁻ ω, leftKernel hC hcirc ρ ω S ∂P :=
  Measure.bind_apply hS hk.aemeasurable

/-- The right measure evaluated on a measurable set (`Measure.bind_apply`). -/
theorem rightMeas_apply {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hk : Measurable (rightKernel P γ hC hcirc)) {S : Set PosObs}
    (hS : MeasurableSet S) :
    rightMeas P γ hC hcirc S = ∫⁻ z in ball (0 : ℂ) 1, rightKernel P γ hC hcirc z S ∂volume :=
  Measure.bind_apply hS hk.aemeasurable

/-- **J7 step 1 (finite-mass version of the LQG measure on `B₁`).** For an `α = 0` LQG measure `μ` of a whole-plane
GFF, there is a measurable family of finite measures `ρ` with `(μ ω).restrict B₁ = ρ ω` almost surely. The family is
`finRestr (Dec ∘ F)`, where `F` is the measurable continuous circle version and `Dec ∘ F` the decoded measure
(`lqgMeasureOfProfileMeasurable_derived`). Its total mass is the mass identity of `DMSFiniteTiltPosStmt` with `n = m = 0`
and `Φ ≡ 1`. -/
theorem exists_restrict_eq_finRestr {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hW : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ 0 hcirc μ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hFin : DMSFiniteTiltPosStmt.{u}) :
    ∃ ρ : Ω → Measure ℂ, Measurable ρ ∧ (∀ ω, IsFiniteMeasure (ρ ω)) ∧
      ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) = ρ ω := by
  obtain ⟨F, hFm, -, hF⟩ := hW.exists_measurable_continuous_circle_version
  obtain ⟨Dec, hDecm, hμDec, -⟩ :=
    lqgMeasureOfProfileMeasurable_derived Ω P γ 0 hC hcirc μ F hW hL hFm hF
  have hμ'm : Measurable (fun ω => Dec (F ω)) := hDecm.comp hFm
  have h1 := hFin Ω P γ hC hcirc μ hW hL hγ0 hγ2 0 0 Fin.elim0 Fin.elim0 (fun _ => 1)
    (fun i => Fin.elim0 i) measurable_const
  have hmass0 : ∫⁻ ω, μ ω (ball (0 : ℂ) 1) ∂P = volume (ball (0 : ℂ) 1) := by
    simpa [lintegral_const, Measure.restrict_apply_univ] using h1
  have hmass : ∫⁻ ω, Dec (F ω) (ball (0 : ℂ) 1) ∂P = volume (ball (0 : ℂ) 1) := by
    rw [← hmass0]
    refine lintegral_congr_ae ?_
    filter_upwards [hμDec] with ω h
    rw [h]
  have hmeasB : Measurable fun ω => Dec (F ω) (ball (0 : ℂ) 1) :=
    (Measure.measurable_coe measurableSet_ball).comp hμ'm
  have hfin : ∀ᵐ ω ∂P, Dec (F ω) (ball (0 : ℂ) 1) < ∞ :=
    ae_lt_top hmeasB (by rw [hmass]; exact measure_ball_lt_top.ne)
  refine ⟨DMSFiniteTiltPosDerived.finRestr (fun ω => Dec (F ω)),
    DMSFiniteTiltPosDerived.measurable_finRestr hμ'm,
    DMSFiniteTiltPosDerived.isFiniteMeasure_finRestr _, ?_⟩
  filter_upwards [hμDec, hfin] with ω h1 h2
  rw [h1]
  simp [DMSFiniteTiltPosDerived.finRestr, h2]

/-- **J7 step 3 (reduction to the measure identity).** If the left and right measures agree, the integrals of every
measurable `Ψ` agree. The left side is first replaced by the finite family `ρ` (`hρμ`), then the three
`lintegral_map` and `Measure.lintegral_bind` steps move the integral to `PosObs`. -/
theorem lintegral_joint_eq_of_measures_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ρ : Ω → Measure ℂ}
    (hρ : Measurable ρ) (hfin : ∀ ω, IsFiniteMeasure (ρ ω))
    (hρμ : ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) = ρ ω)
    (hG : Measurable (obsG hC hcirc)) (hGs : Measurable (obsGs γ hC hcirc))
    (hLR : leftMeas P hC hcirc ρ = rightMeas P γ hC hcirc)
    (Ψ : PosObs → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (obsG hC hcirc (ω, z)) ∂(μ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (obsGs γ hC hcirc (z, ω)) ∂P ∂volume := by
  have hk := measurable_leftKernel hρ hfin hG
  have hk2 := measurable_rightKernel (P := P) hGs
  have hA : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (obsG hC hcirc (ω, z)) ∂(μ ω) ∂P
      = ∫⁻ ω, ∫⁻ x, Ψ x ∂(leftKernel hC hcirc ρ ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hρμ] with ω hω
    have hm : Measurable fun z => obsG hC hcirc (ω, z) := hG.comp measurable_prodMk_left
    rw [leftKernel, lintegral_map hΨ hm, ← hω]
  have hL : ∫⁻ x, Ψ x ∂(leftMeas P hC hcirc ρ) = ∫⁻ ω, ∫⁻ x, Ψ x ∂(leftKernel hC hcirc ρ ω) ∂P :=
    Measure.lintegral_bind hk.aemeasurable hΨ.aemeasurable
  have hR : ∫⁻ x, Ψ x ∂(rightMeas P γ hC hcirc) = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (obsGs γ hC hcirc (z, ω)) ∂P ∂volume := by
    rw [rightMeas, Measure.lintegral_bind hk2.aemeasurable hΨ.aemeasurable]
    refine lintegral_congr fun z => ?_
    have hm : Measurable fun ω => obsGs γ hC hcirc (z, ω) := hGs.comp measurable_prodMk_left
    rw [rightKernel, lintegral_map hΨ hm]
  rw [hA, ← hL, hLR, hR]

end DMSJointPosOfFinite

end HarmonicBalls
