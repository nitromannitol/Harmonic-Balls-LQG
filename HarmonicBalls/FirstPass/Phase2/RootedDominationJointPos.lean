import HarmonicBalls.FirstPass.Phase2.RootedDominationJoint

/-! # Positive-radius joint marked DMS identity and the B2 conditional theorem

This file states the joint marked DMS identity on the positive-radius circles, parametrised by `CircleParameter = Set.Ioi 0 × ℂ`:

* `DMSLemmaA10WholePlaneMarkedJointPos` / `DMSLemmaA10WholePlaneMarkedJointPosStmt`: the candidate input (PENDING TRUTH CHECK; Duplantier-Miller-Sheffield, arXiv:1409.7055, Lemma A.10, marked form). Not a binder of any counted
  theorem and not staged in `Frozen/` or `Proposed/`.
* `localRootedFieldMeasureDomination_of_jointPos_of_shifted`: the B2 conditional theorem, with the joint
  identity `hJoint` in its positive-radius form. The test function is read through the positive-radius extension `posExtend`, which agrees with `posPart`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Zero extension of a positive-radius profile `H : CircleParameter → ℝ` to a profile on `ℝ × ℂ`: the value at `(r, z)`
is `H (r, z)` when `r > 0` and `0` otherwise. For `H = fun p => g p.1 p.2` this is `posPart g`
(`posPart_posExtend`). -/
noncomputable def posExtend (H : CircleParameter → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then H ⟨⟨r, h⟩, z⟩ else 0

lemma posPart_posExtend (g : ℝ → ℂ → ℝ) :
    posPart (posExtend fun p : CircleParameter => g p.1 p.2) = posPart g := by
  funext r z
  by_cases hr : 0 < r
  · simp [posPart, posExtend, hr]
  · simp [posPart, hr]

lemma measurable_posExtend : Measurable fun H : CircleParameter → ℝ => posExtend H := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun z => ?_
  by_cases hr : 0 < r
  · simp only [posExtend, hr, ↓reduceDIte]
    exact measurable_pi_apply (⟨⟨r, hr⟩, z⟩ : CircleParameter)
  · simp only [posExtend, hr, ↓reduceDIte]
    exact measurable_const

/-- **Positive-radius joint marked DMS identity, one instance (candidate input, PENDING TRUTH CHECK).**
Duplantier-Miller-Sheffield, arXiv:1409.7055, Lemma A.10, in the marked form that sees the circle profile only at
positive radii: for a whole-plane GFF `(hC, hcirc)` and the `α = 0` LQG measure `μ` of `hcirc` at parameter `0 < γ < 2`,
and for every measurable test `Ψ` of the triple (pairing, positive-radius circle profile, mark), integrating `Ψ`
against `μ_ω` restricted to the unit ball and against `P` equals integrating the DMS-shifted triple over the mark `z` in
`B₁` and over `P`. -/
def DMSLemmaA10WholePlaneMarkedJointPos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → 0 < γ → γ < 2 →
    ∀ Ψ : (((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, (fun p : CircleParameter => hcirc ω p.1 p.2), z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
              Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0),
                (fun p : CircleParameter => dmsShiftedCircle γ z (hcirc ω) p.1 p.2), z) ∂P ∂volume

/-- The positive-radius joint marked identity for every whole-plane GFF and every `α = 0` LQG measure, in the universe of
the counted statements. This is the shape of the input `hJoint` of `localRootedFieldMeasureDomination_of_jointPos_of_shifted`. -/
def DMSLemmaA10WholePlaneMarkedJointPosStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedJointPos P γ hC hcirc μ

/-- The test function of Step 4 read through the positive-radius extension depends on the profile only through `posPart`,
so the positive-radius form and the original form agree on every profile of the form `fun p => g p.1 p.2`. -/
lemma rootedTestFn_posExtend (r : ℝ) (D : Set ℂ) (S : Set (ℂ × Measure ℂ))
    (Dec : C(CircleParameter, ℝ) → Measure ℂ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (T : (ℂ → ℝ) → ℝ) (g : ℝ → ℂ → ℝ) (z : ℂ) :
    rootedTestFn r D S Dec Sel (T, posExtend (fun p : CircleParameter => g p.1 p.2), z)
      = rootedTestFn r D S Dec Sel (T, g, z) := by
  simp only [rootedTestFn, posPart_posExtend]

lemma measurable_rootedTestFnPos {r : ℝ} {D : Set ℂ} {S : Set (ℂ × Measure ℂ)}
    {Dec : C(CircleParameter, ℝ) → Measure ℂ} {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)}
    (hD : MeasurableSet D) (hS : MeasurableSet S) (hDec : Measurable Dec) (hSel : Measurable Sel) :
    Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (fun x : ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ =>
        rootedTestFn r D S Dec Sel (x.1, posExtend x.2.1, x.2.2)) :=
  (measurable_rootedTestFn hD hS hDec hSel).comp
    (measurable_fst.prodMk ((measurable_posExtend.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)))

/-- **Conditional rooted domination, positive-radius form.** Under the
positive-radius joint identity `DMSLemmaA10WholePlaneMarkedJointPosStmt` (candidate input, PENDING TRUTH CHECK) and the
hypotheses `hProf`, `hSel` and `hShift`. -/
theorem localRootedFieldMeasureDomination_of_jointPos_of_shifted
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hSel : CircleProfileSelectorStmt.{u})
    (hShift : ShiftedDecoderNullTransferStmt.{u}) :
    LocalRootedFieldMeasureDomination.{u} := by
  intro Ω _ P _ γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα hμ hν hlam _ _ _ j _
  -- Selector and measurable profile decoder (Steps 1-2).
  obtain ⟨Sel, hSelM, hSelAe⟩ := hSel Ω P hC hcirc hGFF
  have hFM : Measurable fun ω => Sel (posPart (hcirc ω)) :=
    hSelM.comp (measurable_posPart_comp fun r z hr => hGFF.measurable_circle r z hr)
  obtain ⟨Dec, hDecM, hDecAe, -⟩ :=
    hProf Ω P γ α₀ hC hcirc μ (fun ω => Sel (posPart (hcirc ω))) hGFF hμ hFM hSelAe
  have hlamA : AEMeasurable lam P := hGFF.aemeasurable_lqgMeasure hlam
  obtain ⟨ν', hν'M, hν'ae⟩ := hGFF.aemeasurable_lqgMeasure hν
  have hD : MeasurableSet (localDomain j) := measurableSet_localDomain j
  have hfin : ∀ᵐ ω ∂P, lam ω (ball 0 1) ≠ ⊤ :=
    hlam.mono fun ω h => by
      have := h.isLocallyFiniteMeasure
      exact measure_ball_lt_top.ne
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := hμ.mono fun _ h => h.isLocallyFiniteMeasure
  -- The measurable version `Ostar` of the root observation of the decoded measure (Step 4).
  obtain ⟨Ostar, hOstar⟩ : ∃ O : Ω × ℂ → ℂ × Measure ℂ,
      ∀ x, O x = recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2) :=
    ⟨fun x => recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2), fun _ => rfl⟩
  have hOM : Measurable Ostar := by
    have hfun : Ostar = fun x => recentredOutput (localRadius j) (Dec (Sel (posPart (hcirc x.1))), x.2) :=
      funext hOstar
    rw [hfun]
    exact (measurable_recentredOutput _).comp
      ((hDecM.comp (hFM.comp measurable_fst)).prodMk measurable_snd)
  have hDecAe' : ∀ᵐ ω ∂P, μ ω = Dec (Sel (posPart (hcirc ω))) := hDecAe
  have hgood : ∀ᵐ ω ∂P, μ ω = Dec (Sel (posPart (hcirc ω))) ∧ IsLocallyFiniteMeasure (μ ω) :=
    hDecAe'.and hloc
  have hOeq : localRootObservation μ j =ᵐ[(P ⊗ₘ localRootKernel P lam hlamA).restrict
      (Prod.snd ⁻¹' localDomain j)] Ostar := by
    filter_upwards [ae_restrict_of_ae (ae_fst_of_compProd (localRootKernel P lam hlamA) hgood)] with x hx
    obtain ⟨hμx, hlx⟩ := hx
    have := hlx
    rw [hOstar, ← hμx]
    exact localRootObservation_eq_recentredOutput μ j x.1 (μ x.1) rfl x.2
  -- Null transfer of the reference observations (Step 5-6) and the target set.
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
  -- The positive-radius joint identity (Step 7) and the vanishing of its right-hand side (Steps 8-9).
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
      have hH : ∀ᵐ z ∂(volume : Measure ℂ), ∫⁻ ω, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
          (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P = 0 := by
        filter_upwards [(ae_restrict_iff' hD).mp hzN] with z hz
        by_cases hzD : z ∈ localDomain j
        · have hS := hShift Ω P γ α₀ hC hcirc μ ν hGFF hγ0 hγ2 hα hμ hν Dec Sel hDecM hSelM hDecAe' j z hzD
            T hTM (hz hzD)
          have hae : ∀ᵐ ω ∂P, rootedTestFn (localRadius j) (localDomain j) T Dec Sel
              (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) = 0 := by
            filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS] with ω hω
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
  -- Palm replacement (Step 10-12) and the transfer from `Ostar` to the root observation.
  have hzero := ae_restrict_section_zero_of_lintegral P lam hlamA hfin htM hint
  rw [Measure.map_congr hOeq]
  exact rootedLaw_apply_eq_zero_of_palm P lam hlamA hD Ostar hOM hTM hzero

end HarmonicBalls
