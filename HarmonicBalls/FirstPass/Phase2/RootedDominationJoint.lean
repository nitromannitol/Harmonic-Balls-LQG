import HarmonicBalls.FirstPass.Phase2.RootedDominationDerived
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Closure.LocalRootKernelAc
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.S8c.Measurability

/-! # Joint marked DMS identity: conditional derivation of `LocalRootedFieldMeasureDomination` (Lemma 8.2)


The pairings-only marked identity `DMSLemmaA10WholePlaneMarkedSub` (`FirstPass/Frozen/S11i.lean:59`) sees the field only
through `hC`, while the rooted observation of the α₀-measure needs the circle profile `hcirc` as well. This file states the joint marked identity
`DMSLemmaA10WholePlaneMarkedJoint` (Duplantier-Miller-Sheffield, arXiv:1409.7055, Lemma A.10, marked and with the
circle averages of the shifted field). It is a candidate input: PENDING TRUTH CHECK. It is not a binder of any
counted theorem and is not staged in `Frozen/` or `Proposed/`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The circle averages of the DMS-shifted field `h + f_z + κ`, with `f_z = dmsShift γ z` and the constant
`κ = dmsConstant γ z (h_1(0))`, given the circle averages `hc` of `h`: at radius `r` and centre `x`,
`hc r x + Av_{∂B_r(x)} f_z + κ`. This is the circle-profile companion of `dmsShiftedPairing`. -/
noncomputable def dmsShiftedCircle (γ : ℝ) (z : ℂ) (hc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hc r x + Real.circleAverage (dmsShift γ z) x r + dmsConstant γ z (hc 1 0)

/-- **Joint marked DMS identity (candidate input, PENDING TRUTH CHECK).** Duplantier-Miller-Sheffield,
arXiv:1409.7055, Lemma A.10, in the marked form that also sees the circle profile `hcirc`: for a whole-plane GFF `(hC, hcirc)`
and the `α = 0` LQG measure `μ` of `hcirc` at parameter `0 < γ < 2`, and for every measurable test `Ψ` of the triple
(pairing, circle profile, mark), integrating `Ψ` against `μ_ω` restricted to the unit ball and against `P` equals
integrating the shifted triple over the mark `z` in `B₁` and over `P`. Not a binder of any counted theorem. -/
def DMSLemmaA10WholePlaneMarkedJoint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → 0 < γ → γ < 2 →
    ∀ Ψ : (((ℂ → ℝ) → ℝ) × (ℝ → ℂ → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, hcirc ω, z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
              Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P ∂volume

/-- FALSE AS TYPED (zero/negative-radius circle values are
unconstrained by `IsWholePlaneGFF`); use `DMSLemmaA10WholePlaneMarkedJointPosStmt` (RootedDominationJointPos.lean).

The joint marked identity for every whole-plane GFF and every `α = 0` LQG measure, in the universe of the
counted statements. This is the shape of the input `hJoint` of the conditional theorem. -/
def DMSLemmaA10WholePlaneMarkedJointStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedJoint P γ hC hcirc μ

/-- The normalised root kernel is a finite kernel (it is `weightedRestrictionKernel` with unit weight). -/
instance localRootKernel_isFiniteKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) : IsFiniteKernel (localRootKernel P lam hlam) := by
  unfold localRootKernel
  infer_instance

/-! ## Step 2-3 of route section 5: from the Palm integral to the rooted law -/

/-- **Palm replacement (route Steps 2-3).** The unnormalised Palm measure dominates the rooted law. Let `O` be a
measurable observation of a root `(ω, z)` and `S` a measurable set of observations. If for `P`-a.e. `ω` the set of
roots `z ∈ D` with `O(ω, z) ∈ S` is null for `λ_ω|B₁`, then the rooted law `(P ⊗ₘ K_root).restrict (z ∈ D)` assigns
`S` mass zero. The normalised root kernel `K_root` is a.s. absolutely continuous with respect to `λ_ω|B₁`
(`localRootKernel_ac_ae`, Lemma 8.2 proof). -/
theorem rootedLaw_apply_eq_zero_of_palm {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [SFinite P] (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P)
    {D : Set ℂ} (hD : MeasurableSet D) (O : Ω × ℂ → X) (hO : Measurable O)
    {S : Set X} (hS : MeasurableSet S)
    (hzero : ∀ᵐ ω ∂P, (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' (O ⁻¹' S ∩ Prod.snd ⁻¹' D)) = 0) :
    ((P ⊗ₘ localRootKernel P lam hlam).restrict (Prod.snd ⁻¹' D)).map O S = 0 := by
  have hA : MeasurableSet (O ⁻¹' S ∩ Prod.snd ⁻¹' D) := (hO hS).inter (measurable_snd hD)
  rw [Measure.map_apply hO hS, Measure.restrict_apply (hO hS),
    Measure.compProd_apply hA]
  have hae : ∀ᵐ ω ∂P, localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' (O ⁻¹' S ∩ Prod.snd ⁻¹' D)) = 0 := by
    filter_upwards [localRootKernel_ac_ae P lam hlam, hzero] with ω hac hz
    exact hac hz
  rw [lintegral_congr_ae hae, lintegral_zero]

/-! ## Steps 4-12 (conditional): helpers for the joint-identity route

The conditional theorem takes the joint
identity `DMSLemmaA10WholePlaneMarkedJointStmt` (candidate, PENDING TRUTH CHECK), the frozen profile decoder
`LQGMeasureOfProfileMeasurableFrozen` (`FirstPass/Frozen/S8d.lean:33`), a named measurable circle-profile selector
(`CircleProfileSelectorStmt`) and the intermediate pointwise claim `ShiftedDecoderNullTransferStmt`
(PENDING TRUTH CHECK). -/

/-- The positive-radius part of a circle-average profile, as a pure function (cf. `posCircle`,
`FirstPass/S11aa.lean:72`). -/
noncomputable def posPart (hc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if 0 < r then hc r z else 0

lemma measurable_posPart : Measurable (fun hc : ℝ → ℂ → ℝ => posPart hc) := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun z => ?_
  by_cases hr : 0 < r
  · simp only [posPart, hr, ↓reduceIte]
    exact (measurable_pi_apply z).comp (measurable_pi_apply r)
  · simp only [posPart, hr, ↓reduceIte]
    exact measurable_const

lemma measurable_posPart_comp {Ω : Type*} [MeasurableSpace Ω] {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) :
    Measurable fun ω => posPart (hcirc ω) := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun z => ?_
  by_cases hr : 0 < r
  · simp only [posPart, hr, ↓reduceIte]
    exact h r z hr
  · simp only [posPart, hr, ↓reduceIte]
    exact measurable_const

/-- **Measurable circle-profile selector (named input, PENDING TRUTH CHECK).** For every whole-plane GFF there is
a measurable map `Sel` from positive-radius circle-average profiles to continuous functions on `CircleParameter` that
agrees almost surely with the circle averages at each parameter. Measurable-selection device for `hProf`; its content
is the a.s. continuity of the circle-average process (`IsWholePlaneGFF.ae_continuousOn_circle`) together with a countable
dense family of parameters. Not in the repository. -/
def CircleProfileSelectorStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → ∃ Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ), Measurable Sel ∧
      ∀ p : CircleParameter, (fun ω => Sel (posPart (hcirc ω)) p) =ᵐ[P] fun ω => hcirc ω p.1 p.2

/-- **Intermediate pointwise claim (PENDING TRUTH CHECK; not a frozen input).** Steps 10-11: for a
fixed root `z ∈ D`, a null local reference event of `ν` forces a null event of the decoded DMS-shifted profile,
recentred at `z`. `Dec` and `Sel` are the profile decoder and selector of the identification. -/
def RootedShiftedDecoderNullTransfer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ) (Dec : C(CircleParameter, ℝ) → Measure ℂ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (j : ℕ) : Prop :=
  ∀ z ∈ localDomain j, ∀ S : Set (ℂ × Measure ℂ), MeasurableSet S →
    P {ω | localReferenceObservation ν j (z, ω) ∈ S} = 0 →
      P {ω | recentredOutput (localRadius j)
        (Dec (Sel (posPart (dmsShiftedCircle γ z (hcirc ω)))), z) ∈ S} = 0

/-- **Intermediate hypothesis (PENDING TRUTH CHECK; not a frozen input).** The pointwise claim
`RootedShiftedDecoderNullTransfer` for every measurable decoder and selector that identify the α₀-measure `μ` through
the circle profile. Open point for the operator: whether this universal form is true (decoders are not unique on
DMS-shifted profiles; see the canonical-decoder option (a) of BLOCKED-STEP-C). -/
def ShiftedDecoderNullTransferStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMeasureOfField P γ γ hcirc ν →
    ∀ (Dec : C(CircleParameter, ℝ) → Measure ℂ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)),
      Measurable Dec → Measurable Sel → (∀ᵐ ω ∂P, μ ω = Dec (Sel (posPart (hcirc ω)))) →
      ∀ j : ℕ, RootedShiftedDecoderNullTransfer P γ hcirc ν Dec Sel j

lemma measurableSet_localDomain (j : ℕ) : MeasurableSet (localDomain j) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- A property holding almost surely in `ω` holds almost surely in `x` for the first marginal of `P ⊗ₘ K`. -/
lemma ae_fst_of_compProd {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω} [SFinite P]
    (K : Kernel Ω X) [IsSFiniteKernel K] {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ x ∂(P ⊗ₘ K), p x.1 := by
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  have hae0 : (fun ω => K ω (Prod.mk ω ⁻¹' (t ×ˢ (Set.univ : Set X)))) =ᵐ[P] fun _ => 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp ht0] with ω hω
    have hempty : Prod.mk ω ⁻¹' (t ×ˢ (Set.univ : Set X)) = ∅ := by
      ext x; simp [hω]
    simp [hempty]
  have hset : (P ⊗ₘ K) (t ×ˢ (Set.univ : Set X)) = 0 := by
    rw [Measure.compProd_apply (htm.prod MeasurableSet.univ), lintegral_congr_ae hae0, lintegral_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hset] with x hx
  by_contra hpx
  exact hx ⟨hsub hpx, Set.mem_univ _⟩

/-- Fubini on the rooted reference product: a null set of `(vol|D) ⊗ P` has `P`-null sections for a.e. root. -/
lemma ae_section_null_of_prod_null {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : Set ℂ} {T : Set (ℂ × Ω)} (hT : MeasurableSet T) (h : (volume.restrict D).prod P T = 0) :
    ∀ᵐ z ∂(volume.restrict D), P (Prod.mk z ⁻¹' T) = 0 := by
  rw [Measure.prod_apply hT] at h
  exact (lintegral_eq_zero_iff (measurable_measure_prodMk_left hT)).mp h

/-- On a locally finite value `m = μ ω`, the root observation is the recentred output of `m` (`finitePart` is the
identity on locally finite measures). -/
lemma localRootObservation_eq_recentredOutput {Ω : Type*} (μ : Ω → Measure ℂ) (j : ℕ) (ω : Ω) (m : Measure ℂ)
    (hm : μ ω = m) [IsLocallyFiniteMeasure m] (z : ℂ) :
    localRootObservation μ j (ω, z) = recentredOutput (localRadius j) (m, z) := by
  simp only [localRootObservation, recentredOutput, hm, finitePart_eq_of_locallyFinite]

lemma measurable_restrict_fn (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (fun m : Measure ℂ => m.restrict B) :=
  Measure.measurable_of_measurable_coe _ fun s hs => by
    simp only [Measure.restrict_apply hs]
    exact Measure.measurable_coe (hs.inter hB)

lemma measurable_localReferenceObservation' {Ω : Type*} [MeasurableSpace Ω] {ν : Ω → Measure ℂ}
    (hν : Measurable ν) (j : ℕ) :
    Measurable (localReferenceObservation ν j) :=
  measurable_fst.prodMk ((measurable_massNormalize _).comp
    ((measurable_restrict_fn (ball 0 (localRadius j)) measurableSet_ball).comp (hν.comp measurable_snd)))

/-- The test function of Step 4: the indicator of `D` in the root times the indicator of `S` at the recentred
decoded observation. It depends on the profile only through `Sel (posPart hc)` and on the root through `z`. -/
noncomputable def rootedTestFn (r : ℝ) (D : Set ℂ) (S : Set (ℂ × Measure ℂ))
    (Dec : C(CircleParameter, ℝ) → Measure ℂ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (x : ((ℂ → ℝ) → ℝ) × (ℝ → ℂ → ℝ) × ℂ) : ℝ≥0∞ :=
  D.indicator (fun _ => (1 : ℝ≥0∞)) x.2.2 *
    S.indicator (fun _ => (1 : ℝ≥0∞)) (recentredOutput r (Dec (Sel (posPart x.2.1)), x.2.2))

lemma measurable_rootedTestFn {r : ℝ} {D : Set ℂ} {S : Set (ℂ × Measure ℂ)}
    {Dec : C(CircleParameter, ℝ) → Measure ℂ} {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)}
    (hD : MeasurableSet D) (hS : MeasurableSet S) (hDec : Measurable Dec) (hSel : Measurable Sel) :
    Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (rootedTestFn r D S Dec Sel) := by
  have h1 : Measurable (fun y : (ℝ → ℂ → ℝ) × ℂ => D.indicator (fun _ => (1 : ℝ≥0∞)) y.2 *
      S.indicator (fun _ => (1 : ℝ≥0∞)) (recentredOutput r (Dec (Sel (posPart y.1)), y.2))) :=
    ((measurable_const.indicator hD).comp measurable_snd).mul
      ((measurable_const.indicator hS).comp
        ((measurable_recentredOutput r).comp
          ((hDec.comp (hSel.comp (measurable_posPart.comp measurable_fst))).prodMk measurable_snd)))
  exact h1.comp measurable_snd

/-! ## Conditional rooted domination (Steps 2-6 and 12; PENDING TRUTH CHECK) -/

/-- Normalised restriction times the mass recovers the restriction: `m(B) · (m(B)⁻¹ • m|_B)(A) = m|_B(A)` when
`m(B) < ∞`. -/
lemma mass_mul_normalized_restrict {m : Measure ℂ} {B : Set ℂ} (hfin : m B ≠ ⊤) (A : Set ℂ) :
    m B * ((m B)⁻¹ • m.restrict B) A = m.restrict B A := by
  by_cases h0 : m B = 0
  · have hr : m.restrict B = 0 := Measure.restrict_eq_zero.mpr h0
    simp [hr, h0]
  · rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]

/-- Almost surely the normalised root kernel is the normalised restriction of `λ_ω` to the unit ball (unit weight
of `ae_weightedRestrictionKernel_eq`). -/
lemma ae_localRootKernel_eq_normalized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) :
    ∀ᵐ ω ∂P, localRootKernel P lam hlam ω = ((lam ω) (ball 0 1))⁻¹ • (lam ω).restrict (ball 0 1) := by
  filter_upwards [ae_weightedRestrictionKernel_eq P lam hlam (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const] with ω hω
  have hk : localRootKernel P lam hlam ω =
      normalizedRestriction ((lam ω).withDensity (fun _ => 1)) (ball 0 1) := hω
  have hd : (lam ω).withDensity (fun _ => 1) = lam ω := withDensity_one
  rw [hk, hd]
  rfl

/-- The section masses of the normalised root kernel are measurable in `ω` (it is a finite kernel). -/
lemma measurable_localRootKernel_section {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) {t : Set (Ω × ℂ)} (ht : MeasurableSet t) :
    Measurable fun ω => localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' t) :=
  Kernel.measurable_kernel_prodMk_left ht

/-- **Vanishing of the Palm integral (route Steps 10-12).** If the `λ_ω|B₁`-masses of the sections of a measurable
`t` integrate to zero over `P`, these masses vanish `P`-a.s. The normalised root kernel is `λ_ω|B₁` divided by
`λ_ω(B₁)`, which is finite `P`-a.s., and it is a finite kernel, so the section masses are measurable. -/
lemma ae_restrict_section_zero_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P)
    (hfin : ∀ᵐ ω ∂P, lam ω (ball 0 1) ≠ ⊤) {t : Set (Ω × ℂ)} (ht : MeasurableSet t)
    (hint : ∫⁻ ω, (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' t) ∂P = 0) :
    ∀ᵐ ω ∂P, (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' t) = 0 := by
  have hc : AEMeasurable (fun ω => lam ω (ball 0 1)) P :=
    (Measure.measurable_coe measurableSet_ball).comp_aemeasurable hlam
  have hZ : AEMeasurable (fun ω => localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' t)) P :=
    (measurable_localRootKernel_section P lam hlam ht).aemeasurable
  have hG : (fun ω => (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' t)) =ᵐ[P]
      fun ω => lam ω (ball 0 1) * localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' t) := by
    filter_upwards [ae_localRootKernel_eq_normalized P lam hlam, hfin] with ω hk hf
    rw [hk, mass_mul_normalized_restrict hf]
  have h0 : ∫⁻ ω, lam ω (ball 0 1) * localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' t) ∂P = 0 :=
    (lintegral_congr_ae hG.symm).trans hint
  have hcZ := (lintegral_eq_zero_iff' (hc.mul hZ)).mp h0
  filter_upwards [hG, hcZ] with ω hGω hω
  exact hGω.trans hω

/-- **Fubini on the rooted reference product (route Step 5).** A `((vol|D_j) ⊗ P)`-null set of reference observations
has `P`-null sections for almost every root `z ∈ D_j`. The `P`-a.s. identity `ν = ν'` (`ν'` measurable) transfers to
the reference observations. -/
lemma ae_section_ref_null {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (j : ℕ)
    {ν ν' : Ω → Measure ℂ} (hν' : Measurable ν') (hae : ν =ᵐ[P] ν') {T : Set (ℂ × Measure ℂ)}
    (hT : MeasurableSet T)
    (h0 : ((volume.restrict (localDomain j)).prod P).map (localReferenceObservation ν j) T = 0) :
    ∀ᵐ z ∂(volume.restrict (localDomain j)), P {ω | localReferenceObservation ν j (z, ω) ∈ T} = 0 := by
  have hV' : Measurable (localReferenceObservation ν' j) := measurable_localReferenceObservation' hν' j
  have hXY : localReferenceObservation ν j =ᵐ[(volume.restrict (localDomain j)).prod P]
      localReferenceObservation ν' j := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volume.restrict (localDomain j)) (ν := P)).ae hae]
      with x hx
    simp only [localReferenceObservation, hx]
  rw [Measure.map_congr hXY, Measure.map_apply hV' hT] at h0
  filter_upwards [ae_section_null_of_prod_null (hV' hT) h0] with z hz
  have hset : {ω | localReferenceObservation ν j (z, ω) ∈ T} =ᵐ[P]
      {ω | localReferenceObservation ν' j (z, ω) ∈ T} := by
    refine Filter.eventuallyEqSet_iff.mpr ?_
    filter_upwards [hae] with ω hω
    simp only [localReferenceObservation, hω]
  rw [measure_congr hset]
  exact hz

/-- SUPERSEDED: takes the FALSE hJoint; use `localRootedFieldMeasureDomination_of_jointPos_of_shifted`
(RootedDominationJointPos.lean).

**Conditional rooted domination.** From the
joint marked DMS identity `hJoint` (Duplantier-Miller-Sheffield, arXiv:1409.7055, Lemma A.10; PENDING TRUTH CHECK), the
measurable profile decoder `hProf` (`LQGMeasureOfProfileMeasurableFrozen`), the circle-profile selector `hSel`
(PENDING TRUTH CHECK) and the shifted decoder transfer `hShift` (PENDING TRUTH CHECK), the local rooted comparison
`LocalRootedFieldMeasureDomination` (Lemma 8.2 of arXiv:2208.11795, proof) follows. -/
theorem localRootedFieldMeasureDomination_of_joint_of_shifted
    (hJoint : DMSLemmaA10WholePlaneMarkedJointStmt.{u})
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
  -- The joint identity (Step 7) and the vanishing of its right-hand side (Steps 8-9).
  have hint : ∫⁻ ω, (lam ω).restrict (ball 0 1)
      (Prod.mk ω ⁻¹' (Ostar ⁻¹' T ∩ Prod.snd ⁻¹' localDomain j)) ∂P = 0 := by
    have hJ := hJoint Ω P γ hC hcirc lam hGFF hlam hγ0 hγ2
      (rootedTestFn (localRadius j) (localDomain j) T Dec Sel)
      (measurable_rootedTestFn hD hTM hDecM hSelM)
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
