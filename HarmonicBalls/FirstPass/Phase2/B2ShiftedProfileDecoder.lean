import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived

/-! # B2 shifted-profile decoder: canonical decoder property and the success at a.e. root (MQ-lh-15)

Task `fp-phase2-rooted-continuity-and-shifted-decoder`, part (3); worker z3. Route: MATH-ANSWERS.md l.158-183 (verdict
TRUE-AFTER-FIX, option (a) for the explicit canonical decoder `ProfileDecoderDerived.decoder`).

* `CanonicalDecoderLimitStmt` and `canonicalDecoder_limit`: the additional Lean statement of l.161-165, proved by its
  step 2 (existence of a limit gives membership in `convSet`, then `isLQGLimit_decoder`).
* `shifted_selected_lintegral_eq_zero` and `shifted_selected_mem_convSet_ae_root`: step 4 of l.170-183, the joint identity
  applied to the complement of the Borel convergence locus. The joint identity is the positive-radius form
  `DMSLemmaA10WholePlaneMarkedJointPosStmt` (candidate, PENDING R26), taken as an explicit hypothesis; the false
  `DMSLemmaA10WholePlaneMarkedJointStmt` is not used. The joint identity is stated for the `α = 0` measure only, so
  the convergence locus is `convSet T γ 0`.
* The a.e.-root upgrade needs the joint measurability hypothesis `hJM`. It is a named BLOCKED-STEP: the answer does not
  give an argument for it.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- **Canonical decoder property (MQ-lh-15 answer, l.161-165; TRUE-AFTER-FIX, option (a)).** For the explicit canonical
decoder `ProfileDecoderDerived.decoder T γ α`, every continuous positive-radius profile `y` whose circle-average LQG
limit exists has the LQG limit `decoder T γ α y`. -/
def CanonicalDecoderLimitStmt (T : ProfileDecoderDerived.TestFamily) (γ α : ℝ) : Prop :=
  ∀ y : C(CircleParameter, ℝ),
    (∃ m, IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) m) →
      IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) (ProfileDecoderDerived.decoder T γ α y)

/-- The canonical decoder has the property `CanonicalDecoderLimitStmt` (MQ-lh-15, route step 2): an existing limit gives
membership in the convergence locus `convSet` (apply the convergence to each test function `T.D n`), and then
`isLQGLimit_decoder` identifies the output. -/
theorem canonicalDecoder_limit (T : ProfileDecoderDerived.TestFamily) (γ α : ℝ) :
    CanonicalDecoderLimitStmt T γ α := by
  rintro y ⟨m, hm⟩
  refine ProfileDecoderDerived.isLQGLimit_decoder T γ α fun n => ?_
  exact ⟨_, hm.tendsto_integral (T.D n) (T.D n).continuous (T.D n).hasCompactSupport⟩

/-- The positive-radius extension of a coordinate profile is the positive part of the profile. -/
lemma posExtend_coe_eq (g : ℝ → ℂ → ℝ) :
    posExtend (fun p : CircleParameter => g p.1 p.2) = posPart g := by
  funext r z
  by_cases hr : 0 < r
  · simp [posExtend, posPart, hr]
  · simp [posExtend, posPart, hr]

/-- **Step 4 core (MQ-lh-15 answer, l.170-183): the joint identity transfers the convergence locus.** Let `E` be the
complement of the convergence locus `convSet T γ 0`. The joint identity, applied to the test `1_E (Sel (posExtend H))`,
gives the vanishing of the lower integral over the unit ball of the selected DMS-shifted profile lying in `E`. The
original-law profile lies in the convergence locus almost surely, since `μ` is its LQG measure. -/
theorem shifted_selected_lintegral_eq_zero
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (hSelM : Measurable Sel)
    (hSelAe : ∀ p : CircleParameter, (fun ω => Sel (posPart (hcirc ω)) p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, (ProfileDecoderDerived.convSet T γ 0)ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
        (Sel (posPart (dmsShiftedCircle γ z (hcirc ω)))) ∂P ∂volume = 0 := by
  have hEM : MeasurableSet (ProfileDecoderDerived.convSet T γ 0)ᶜ :=
    (ProfileDecoderDerived.measurableSet_convSet T γ 0).compl
  -- a.s. the selected profile is the profile of the field, hence lies in the convergence locus (as `μ` is its limit)
  have hagree : ∀ᵐ ω ∂P, ∀ p : CircleParameter, Sel (posPart (hcirc ω)) p = hcirc ω p.1 p.2 :=
    IsWholePlaneGFF.ae_circle_map_eq_raw (F := fun ω => Sel (posPart (hcirc ω))) hGFF hSelAe
  have h2 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (circleProfile (Sel (posPart (hcirc ω))))) (μ ω) :=
    (isLQGMeasureOfField_circleProfile_iff hagree γ 0 μ).1 hμ
  have hmem : ∀ᵐ ω ∂P, Sel (posPart (hcirc ω)) ∈ ProfileDecoderDerived.convSet T γ 0 := by
    filter_upwards [h2] with ω hω
    intro m
    exact ⟨_, hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport⟩
  -- The test function `Ψ(T, H, z) = 1_E (Sel (posExtend H))`, measurable for the joint identity.
  let Ψ : ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ → ℝ≥0∞ := fun x =>
    (ProfileDecoderDerived.convSet T γ 0)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (Sel (posExtend x.2.1))
  have hΨM : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ :=
    (measurable_const.indicator hEM).comp
      (hSelM.comp (measurable_posExtend.comp (measurable_fst.comp measurable_snd)))
  have hJ := hJoint Ω P γ hC hcirc μ hGFF hμ hγ0 hγ2 Ψ hΨM
  -- The left side vanishes almost surely: the inner integrand is zero for every ω with the convergence property.
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, (fun p : CircleParameter => hcirc ω p.1 p.2), z) ∂(μ ω) ∂P
      = 0 := by
    have hz : ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, (fun p : CircleParameter => hcirc ω p.1 p.2), z) ∂(μ ω)
        = 0 := by
      filter_upwards [hmem] with ω hω
      have h0 : ∀ z, Ψ (hC ω, (fun p : CircleParameter => hcirc ω p.1 p.2), z) = 0 := fun z => by
        simp [Ψ, posExtend_coe_eq, hω]
      simp [h0]
    rw [lintegral_congr_ae hz, lintegral_zero]
  -- Transfer of the right side: `posExtend` of the DMS-shifted profile is its positive part.
  calc _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0),
            (fun p : CircleParameter => dmsShiftedCircle γ z (hcirc ω) p.1 p.2), z) ∂P ∂volume := by
        simp only [Ψ, posExtend_coe_eq]
    _ = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, (fun p : CircleParameter => hcirc ω p.1 p.2), z) ∂(μ ω) ∂P :=
        hJ.symm
    _ = 0 := hL

/-- **Success at a.e. root (MQ-lh-15 answer, l.170-183, route step 4).** Original-law success gives shifted success:
for Lebesgue-a.e. root `z` in the unit ball, almost surely the selected DMS-shifted profile lies in the convergence
locus `convSet T γ 0`. The measurability hypothesis `hJM` (joint measurability of `(z, ω) ↦ Sel (posPart (dms))`)
is a named BLOCKED-STEP: the answer gives no argument for it (MQ-lh-15 step 4 implicitly needs it). -/
theorem shifted_selected_mem_convSet_ae_root
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (hSelM : Measurable Sel)
    (hSelAe : ∀ p : CircleParameter, (fun ω => Sel (posPart (hcirc ω)) p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (hJM : Measurable fun q : ℂ × Ω => Sel (posPart (dmsShiftedCircle γ q.1 (hcirc q.2)))) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      Sel (posPart (dmsShiftedCircle γ z (hcirc ω))) ∈ ProfileDecoderDerived.convSet T γ 0 := by
  have hL := shifted_selected_lintegral_eq_zero hJoint T γ hγ0 hγ2 P hC hcirc μ hGFF hμ Sel hSelM hSelAe
  have hEM : MeasurableSet (ProfileDecoderDerived.convSet T γ 0)ᶜ :=
    (ProfileDecoderDerived.measurableSet_convSet T γ 0).compl
  have hG : Measurable fun z : ℂ => ∫⁻ ω, (ProfileDecoderDerived.convSet T γ 0)ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
      (Sel (posPart (dmsShiftedCircle γ z (hcirc ω)))) ∂P :=
    ((measurable_const.indicator hEM).comp hJM).lintegral_prod_right'
  have hz := (lintegral_eq_zero_iff hG).1 hL
  filter_upwards [hz] with z hz0
  have hfz : Measurable fun ω : Ω => (ProfileDecoderDerived.convSet T γ 0)ᶜ.indicator (fun _ => (1 : ℝ≥0∞))
      (Sel (posPart (dmsShiftedCircle γ z (hcirc ω)))) :=
    (measurable_const.indicator hEM).comp (hJM.comp (measurable_const.prodMk measurable_id))
  have hae := (lintegral_eq_zero_iff hfz).1 hz0
  filter_upwards [hae] with ω hω
  by_contra hn
  have hE : Sel (posPart (dmsShiftedCircle γ z (hcirc ω))) ∈ (ProfileDecoderDerived.convSet T γ 0)ᶜ := hn
  simp [Set.indicator_of_mem hE] at hω

end HarmonicBalls
