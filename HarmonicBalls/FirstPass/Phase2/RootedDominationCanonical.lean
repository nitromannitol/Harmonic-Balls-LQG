import HarmonicBalls.FirstPass.Phase2.CanonicalDecoderIdentity
import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferDerived
import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.FirstPass.Phase2.DMSJointPosOfFinite

/-! # Canonical form of the rooted domination

* `rootedFieldMeasureDomination_of_ae_null`: the conditional rooted domination of
  `localRootedFieldMeasureDomination_of_jointPos_of_shifted` for an arbitrary measurable decoder `Dec` and selector `Sel`
  of the α₀-measure `μ`, with the null transfer in its almost-every-root form (the form of
  `RootedShiftedDecoderNullTransferCanonical`). The proof is that of `localRootedFieldMeasureDomination_of_jointPos_of_shifted`:
  the existentials `Sel` (from `hSel`, RootedDominationJointPos.lean:99) and `Dec` (from `hProf`, :102-103) are replaced by the
  given `Dec` and `Sel`, and the pointwise null transfer `hShift` (:171) by its almost-every-root form.
* `localRootedFieldMeasureDomination_canonical_data`: for one measure, with the canonical decoder
  `ProfileDecoderDerived.decoder canonicalTest γ α₀` and selector `canonicalSel`, the identity `hId` of `μ` (the
  premise of `ShiftedDecoderNullTransferCanonicalStmt`) and the canonical null transfer `hShift`. The premises
  `LQGMeasureExistence` of `hShift` are witnessed by `μ` and `lam`; its premise `DMSLemmaA10WholePlaneMarked` is
  `dmsA10Marked_of_sub` applied to `hSub` (DMSLemmaA10WholePlaneMarkedSub, FirstPass/Frozen/S11i.lean:57).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- **Rooted domination from the joint identity and the a.e.-root null transfer.** For an arbitrary measurable decoder
`Dec` and selector `Sel` of the α₀-measure `μ` (a.s. `μ ω = Dec (Sel (posPart (hcirc ω)))`), the null transfer of the
reference observation in its almost-every-root form gives the absolute continuity of the rooted law of `μ` with respect to
the reference law of `ν`. Duplantier-Miller-Sheffield Lemma A.10 enters only through `hJoint`. -/
theorem rootedFieldMeasureDomination_of_ae_null
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (Dec : C(CircleParameter, ℝ) → Measure ℂ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (hDecM : Measurable Dec) (hSelM : Measurable Sel)
    (hDecAe : ∀ᵐ ω ∂P, μ ω = Dec (Sel (posPart (hcirc ω))))
    (j : ℕ)
    (hS : ∀ᵐ z ∂(volume.restrict (localDomain j)), ∀ S : Set (ℂ × Measure ℂ), MeasurableSet S →
      P {ω | localReferenceObservation ν j (z, ω) ∈ S} = 0 →
        P {ω | recentredOutput (localRadius j)
          (Dec (Sel (posPart (dmsShiftedCircle γ z (hcirc ω)))), z) ∈ S} = 0) :
    ((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
        (Prod.snd ⁻¹' localDomain j)).map (localRootObservation μ j) ≪
      ((volume.restrict (localDomain j)).prod P).map (localReferenceObservation ν j) := by
  have hFM : Measurable fun ω => Sel (posPart (hcirc ω)) :=
    hSelM.comp (measurable_posPart_comp fun r z hr => hGFF.measurable_circle r z hr)
  have hlamA : AEMeasurable lam P := hGFF.aemeasurable_lqgMeasure hlam
  obtain ⟨ν', hν'M, hν'ae⟩ := hGFF.aemeasurable_lqgMeasure hν
  have hD : MeasurableSet (localDomain j) := measurableSet_localDomain j
  have hfin : ∀ᵐ ω ∂P, lam ω (ball 0 1) ≠ ⊤ :=
    hlam.mono fun ω h => by
      have := h.isLocallyFiniteMeasure
      exact measure_ball_lt_top.ne
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := hμ.mono fun _ h => h.isLocallyFiniteMeasure
  -- The measurable version `Ostar` of the root observation of the decoded measure.
  obtain ⟨Ostar, hOstar⟩ : ∃ O : Ω × ℂ → ℂ × Measure ℂ,
      ∀ x, O x = recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2) :=
    ⟨fun x => recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2), fun _ => rfl⟩
  have hOM : Measurable Ostar := by
    have hfun : Ostar = fun x => recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2) :=
      funext hOstar
    rw [hfun]
    exact (measurable_recentredOutput _).comp
      ((hDecM.comp (hFM.comp measurable_fst)).prodMk measurable_snd)
  have hgood : ∀ᵐ ω ∂P, μ ω = Dec (Sel (posPart (hcirc ω))) ∧ IsLocallyFiniteMeasure (μ ω) :=
    hDecAe.and hloc
  have hOeq : localRootObservation μ j =ᵐ[(P ⊗ₘ localRootKernel P lam hlamA).restrict
      (Prod.snd ⁻¹' localDomain j)] Ostar := by
    filter_upwards [ae_restrict_of_ae (ae_fst_of_compProd (localRootKernel P lam hlamA) hgood)] with x hx
    obtain ⟨hμx, hlx⟩ := hx
    have := hlx
    rw [hOstar, ← hμx]
    exact localRootObservation_eq_recentredOutput μ j x.1 (μ x.1) rfl x.2
  -- Null transfer of the reference observations and the target set.
  refine Measure.AbsolutelyContinuous.mk fun T hTM hT0 => ?_
  have hzN := ae_section_ref_null j hν'M hν'ae hTM hT0
  have htM : MeasurableSet (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j) :=
    (hOM hTM).inter (measurable_snd hD)
  have hind : ∀ ω z, rootedTestFn (localRadius j) (localDomain j) T Dec Sel (hC ω, hcirc ω, z) =
      (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)).indicator 1 z := by
    intro ω z
    have hO : Ostar (ω, z) = recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc ω))), z) :=
      hOstar (ω, z)
    by_cases hz : z ∈ localDomain j <;> by_cases hT' : recentredOutput (localRadius j)
        (Dec (Sel (posPart (hcirc ω))), z) ∈ T <;>
      simp [rootedTestFn, hO, hz, hT']
  have hLHS : ∀ ω, ∫⁻ z in ball (0 : ℂ) 1,
      rootedTestFn (localRadius j) (localDomain j) T Dec Sel (hC ω, hcirc ω, z) ∂(lam ω) =
        (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)) := by
    intro ω
    calc ∫⁻ z in ball (0 : ℂ) 1,
          rootedTestFn (localRadius j) (localDomain j) T Dec Sel (hC ω, hcirc ω, z) ∂(lam ω)
        = ∫⁻ z, (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)).indicator 1 z
            ∂((lam ω).restrict (ball 0 1)) := lintegral_congr fun z => hind ω z
      _ = _ := lintegral_indicator_one (measurable_prodMk_left htM)
  -- The positive-radius joint identity and the vanishing of its right-hand side.
  have hint : ∫⁻ ω, (lam ω).restrict (ball 0 1)
      (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)) ∂P = 0 := by
    have hJ0 := hJoint Ω P γ hC hcirc lam hGFF hlam hγ0 hγ2
      (fun x => rootedTestFn (localRadius j) (localDomain j) T Dec Sel (x.1, posExtend x.2.1, x.2.2))
      (measurable_rootedTestFnPos hD hTM hDecM hSelM)
    have hJ : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1,
        rootedTestFn (localRadius j) (localDomain j) T Dec Sel (hC ω, hcirc ω, z) ∂(lam ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
              (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P ∂volume := by
      simpa only [rootedTestFn_posExtend] using hJ0
    have hRHS : ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
        (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P ∂volume = 0 := by
      have hzN' := (ae_restrict_iff' hD).mp hzN
      have hSA := (ae_restrict_iff' hD).mp hS
      have hH : ∀ᵐ z ∂(volume : Measure ℂ), ∫⁻ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
          (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P = 0 := by
        filter_upwards [hzN', hSA] with z hz hSz
        by_cases hzD : z ∈ localDomain j
        · have hS' := hSz hzD T hTM (hz hzD)
          have hae : ∀ᵐ ω ∂P, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
              (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) = 0 := by
            filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS'] with ω hω
            simp [rootedTestFn, hzD, hω]
          rw [lintegral_congr_ae hae, lintegral_zero]
        · have h0 : ∀ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
              (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) = 0 :=
            fun ω => by simp [rootedTestFn, hzD]
          simp [h0]
      rw [lintegral_congr_ae (ae_restrict_of_ae hH), lintegral_zero]
    calc ∫⁻ ω, (lam ω).restrict (ball 0 1)
          (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)) ∂P
        = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1,
            rootedTestFn (localRadius j) (localDomain j) T Dec Sel (hC ω, hcirc ω, z) ∂(lam ω) ∂P :=
          lintegral_congr fun ω => (hLHS ω).symm
      _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
            (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P ∂volume := hJ
      _ = 0 := hRHS
  -- Palm replacement and the transfer from `Ostar` to the root observation.
  have hzero := ae_restrict_section_zero_of_lintegral P lam hlamA hfin htM hint
  rw [Measure.map_congr hOeq]
  exact rootedLaw_apply_eq_zero_of_palm P lam hlamA hD Ostar hOM hTM hzero

/-- **Canonical rooted domination for one measure.** The canonical decoder `decoder canonicalTest γ α₀` and the canonical
selector `canonicalSel` identify the α₀-measure `μ` (the premise `hId`), and the canonical null transfer
`ShiftedDecoderNullTransferCanonicalStmt` gives the almost-every-root null transfer. The premises of that statement are
supplied as follows: the existence premises by `μ` and `lam`, and `DMSLemmaA10WholePlaneMarked` by `dmsA10Marked_of_sub`
from `hSub` at the fixed `0 < γ < 2`. -/
theorem localRootedFieldMeasureDomination_canonical_data
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hShift : ShiftedDecoderNullTransferCanonicalStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hId : ∀ᵐ ω ∂P, μ ω = ProfileDecoderDerived.decoder canonicalTest γ α₀
      (canonicalSel (posPart (hcirc ω))))
    (j : ℕ) :
    ((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
        (Prod.snd ⁻¹' localDomain j)).map (localRootObservation μ j) ≪
      ((volume.restrict (localDomain j)).prod P).map (localReferenceObservation ν j) :=
  rootedFieldMeasureDomination_of_ae_null hJoint P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hμ hν hlam
    (ProfileDecoderDerived.decoder canonicalTest γ α₀) canonicalSel
    (ProfileDecoderDerived.measurable_decoder canonicalTest γ α₀) canonicalSel_measurable hId j
    (hShift Ω P γ α₀ hC hcirc μ ν hGFF hγ0 hγ2 hα hμ hν
      (fun _ _ _ _ => ⟨lam, hlam⟩) (fun _ _ _ _ => ⟨μ, hμ⟩)
      (fun μ' => hSub Ω P γ hC hcirc μ') hId j)

/-- **Canonical rooted domination, conditional form.** The conditional theorem
`localRootedFieldMeasureDomination_of_jointPos_of_shifted` in its canonical form: the decoder and selector of the
α₀-measure are the canonical `ProfileDecoderDerived.decoder canonicalTest γ α₀` and `canonicalSel`, identified by
`CanonicalDecoderIdentityStmt` (its existence premise is witnessed by `μ`), and the null transfer is the canonical
`ShiftedDecoderNullTransferCanonicalStmt`. The joint identity `hJoint` and the Lemma A.10 input `hSub` stay hypotheses.
The conclusion is that of `LocalRootedFieldMeasureDomination`. -/
theorem localRootedFieldMeasureDomination_canonical_of_shifted
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hId : CanonicalDecoderIdentityStmt.{u})
    (hShift : ShiftedDecoderNullTransferCanonicalStmt.{u}) :
    LocalRootedFieldMeasureDomination.{u} := by
  intro Ω _ P _ γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα hμ hν hlam _ _ _ j _
  exact localRootedFieldMeasureDomination_canonical_data hJoint hSub hShift P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα
    hμ hν hlam (hId Ω P γ α₀ hC hcirc μ hGFF hγ0 hγ2 hα hμ (fun _ _ _ _ => ⟨μ, hμ⟩)) j

/-- **Canonical rooted domination with the derived canonical null transfer.** Same as
`localRootedFieldMeasureDomination_canonical_of_shifted`, with `hShift` discharged by
`shiftedDecoderNullTransferCanonicalStmt_derived` (RootedShiftedNullTransferDerived.lean). Only `hJoint`, `hSub` and the
canonical identity `hId` remain hypotheses. -/
theorem localRootedFieldMeasureDomination_canonical
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ)
    (hId : CanonicalDecoderIdentityStmt.{u}) :
    LocalRootedFieldMeasureDomination.{u} :=
  localRootedFieldMeasureDomination_canonical_of_shifted hJoint hSub hId shiftedDecoderNullTransferCanonicalStmt_derived

/-- **Canonical rooted domination, with the joint identity derived.** The conditional theorem
`localRootedFieldMeasureDomination_canonical` with `hJoint` discharged by `DMSJointPosOfFinite.dMSJointPos_of_sub hSub`
(Duplantier-Miller-Sheffield Lemma A.10, joint identity from the finite tilt family). The canonical decoder identity is
the derived `canonicalDecoderIdentityStmt_derived`, and the null transfer is derived. The only remaining input is the
pending Lemma A.10 subcritical pairing input `hSub` (`DMSLemmaA10WholePlaneMarkedSub`, FirstPass/Frozen/S11i.lean:57,
source-check open). -/
theorem localRootedFieldMeasureDomination_of_sub
    (hSub : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) :
    LocalRootedFieldMeasureDomination.{u} :=
  localRootedFieldMeasureDomination_canonical (DMSJointPosOfFinite.dMSJointPos_of_sub hSub) hSub
    canonicalDecoderIdentityStmt_derived

end HarmonicBalls
