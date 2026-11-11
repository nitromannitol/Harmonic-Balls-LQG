import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.RootedDominationJoint
import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos
import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferSteps
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2
import HarmonicBalls.FirstPass.Phase2.GFFJointLaw
import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.FirstPass.S8c.Measurability
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Proofs.Sec2.AffineField

/-! # Law comparison for the rooted shifted null transfer (MQ-lh-29, step L6)

Step L6 of `notes/fp-gaps/MATH-ANSWERS.md` (section MQ-lh-29): the law of the rooted output `W` built from the
Cameron-Martin shifted field is absolutely continuous with respect to the law of the reference observation.

* `rootOutputOfProfile` is the rooted output `(z, N_r((Dec (Sel (posPart c))) restricted to B_r(0)))` of a profile `c`;
* `rootShiftOutput` is the map `W` of step L5: the output of the profile `c_ω(s, x) = h_s(x - z) - h_1(z) + Av_x(gt)_s`,
  the Gaussian circle-average process of the affine pullback shifted by the test function `gt`.

The positive-radius part of a profile is `posPart` (`RootedDominationJoint.lean`); `extPos` is its inverse on the
index set `{p : ℝ × ℂ // 0 < p.1}` of the joint sample (`GFFJointLaw.jointSample`). -/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal

universe u

namespace HarmonicBalls

namespace RootedShiftedNullTransferLaw

/-- Zero extension of a function on the positive-radius index set `{p : ℝ × ℂ // 0 < p.1}` (the circle-average
coordinates of the joint sample `GFFJointLaw.jointSample`) to a profile `ℝ → ℂ → ℝ`. -/
noncomputable def extPos (F : {p : ℝ × ℂ // 0 < p.1} → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => if h : 0 < r then F ⟨(r, z), h⟩ else 0

/-- The rooted output of a circle-average profile `c` at the root `z`, with decoder `T g g` and canonical selector
`Sel`: `(z, N_r(Dec(Sel(posPart c)) |_{B_r(0)}))`, where `N_r` is `massNormalize r` (the normalisation of
`localReferenceObservation`, `S8c/LocalObservation.lean`). -/
noncomputable def rootOutputOfProfile (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) (c : ℝ → ℂ → ℝ) : ℂ × Measure ℂ :=
  (z, massNormalize r ((ProfileDecoderDerived.decoder T γ γ (Sel (posPart c))).restrict (ball (0 : ℂ) r)))

/-- The map `W` of step L5 of MQ-lh-29: `W ω = rootOutputOfProfile` of the Cameron-Martin shifted circle-average
profile `s x ↦ affineCircle hcirc 1 z ω s x + Av_x(gt)_s` (the circle averages of `h'(· + z) + gt`, with `h'` the
affine pullback of the whole-plane GFF `hcirc` at the root `z`). -/
noncomputable def rootShiftOutput {Ω : Type*} (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) (hcirc : Ω → ℝ → ℂ → ℝ) (gt : ℂ → ℝ) :
    Ω → ℂ × Measure ℂ :=
  fun ω => rootOutputOfProfile T γ Sel r z
    (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s)

lemma measurable_extPos : Measurable extPos := by
  refine measurable_pi_iff.mpr fun r => measurable_pi_iff.mpr fun z => ?_
  by_cases hr : 0 < r
  · simp only [extPos, hr, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [extPos, hr, ↓reduceDIte]
    exact measurable_const

lemma extPos_restrict (c : ℝ → ℂ → ℝ) : extPos (fun p : {p : ℝ × ℂ // 0 < p.1} => c p.1.1 p.1.2) = posPart c := by
  funext r z
  by_cases hr : 0 < r <;> simp [extPos, posPart, hr]

lemma posPart_posPart (c : ℝ → ℂ → ℝ) : posPart (posPart c) = posPart c := by
  funext r z
  by_cases hr : 0 < r <;> simp [posPart, hr]

lemma posPart_eq_posExtend (c : ℝ → ℂ → ℝ) :
    posPart c = posExtend (fun p : CircleParameter => c p.1.1 p.2) := by
  funext r z
  by_cases hr : 0 < r <;> simp [posPart, posExtend, hr]

lemma measurable_restrict_ball (r : ℝ) : Measurable (fun η : Measure ℂ => η.restrict (ball (0 : ℂ) r)) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter measurableSet_ball)

lemma measurable_rootOutputOfProfile (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (hSelM : Measurable Sel) (r : ℝ) (z : ℂ) :
    Measurable (rootOutputOfProfile T γ Sel r z) := by
  unfold rootOutputOfProfile
  refine measurable_const.prodMk ?_
  exact (measurable_massNormalize r).comp ((measurable_restrict_ball r).comp
    ((ProfileDecoderDerived.measurable_decoder T γ γ).comp (hSelM.comp measurable_posPart)))

lemma rootOutputOfProfile_posPart (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) (c : ℝ → ℂ → ℝ) :
    rootOutputOfProfile T γ Sel r z (posPart c) = rootOutputOfProfile T γ Sel r z c := by
  unfold rootOutputOfProfile
  rw [posPart_posPart]

/-- Measurability of the rooted output `W` of step L5 (step (iii) of MQ-lh-29 L6). Only the coordinates of positive
radius of the circle-average process enter, through `posPart`, so the measurability of `hcirc` at positive radii
(`IsWholePlaneGFF.measurable_circle`) suffices. -/
lemma measurable_rootShiftOutput {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (hSelM : Measurable Sel)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (r : ℝ) (z : ℂ) (gt : ℂ → ℝ) :
    Measurable (rootShiftOutput T γ Sel r z hcirc gt) := by
  have hpp : Measurable fun ω => posPart (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s) := by
    refine measurable_pi_iff.mpr fun s => measurable_pi_iff.mpr fun x => ?_
    by_cases hs : 0 < s
    · simp only [posPart, hs, ↓reduceIte]
      have h1 : 0 < ‖(1 : ℂ)‖ * s := by simp [hs]
      have h2 : 0 < ‖(1 : ℂ)‖ := by simp
      exact ((hGFF.measurable_circle _ _ h1).sub (hGFF.measurable_circle _ _ h2)).add_const _
    · simp only [posPart, hs, ↓reduceIte]
      exact measurable_const
  have hfun : rootShiftOutput T γ Sel r z hcirc gt = fun ω => rootOutputOfProfile T γ Sel r z
      (posPart (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s)) := by
    funext ω
    exact (rootOutputOfProfile_posPart T γ Sel r z _).symm
  rw [hfun]
  exact (measurable_rootOutputOfProfile T γ hSelM r z).comp hpp


/-- `extPos` of a joint-sample circle component is the rooted profile of its underlying function. -/
lemma rootOutputOfProfile_extPos (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) (c : ℝ → ℂ → ℝ) :
    rootOutputOfProfile T γ Sel r z (extPos (fun p : {p : ℝ × ℂ // 0 < p.1} => c p.1.1 p.1.2)) =
      rootOutputOfProfile T γ Sel r z c := by
  rw [extPos_restrict, rootOutputOfProfile_posPart]

/-- The rooted output as a function of a joint sample `(pairings, circle averages)` on the index sets of
`GFFJointLaw.jointSample`. -/
noncomputable def rootOutputOfJoint (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ)
    (x : ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ)) : ℂ × Measure ℂ :=
  rootOutputOfProfile T γ Sel r z (extPos x.2)

lemma measurable_rootOutputOfJoint (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    {Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)} (hSelM : Measurable Sel) (r : ℝ) (z : ℂ) :
    Measurable (rootOutputOfJoint T γ Sel r z) :=
  (measurable_rootOutputOfProfile T γ hSelM r z).comp (measurable_extPos.comp measurable_snd)

/-- The Cameron-Martin shifted joint sample at the root `z`: the pairings and circle averages of the affine pullback
`(affinePairing hC hcirc 1 z, affineCircle hcirc 1 z)` shifted by the test function `gt`. -/
noncomputable def affineShiftedJoint {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ)
    (gt : ℂ → ℝ) :
    Ω → ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ) :=
  fun ω => (fun φ => addFunPairing (affinePairing hC hcirc 1 z ω) gt φ.1,
    fun p => affineCircle hcirc 1 z ω p.1.1 p.1.2 + Real.circleAverage gt p.1.2 p.1.1)

lemma measurable_affineShiftedJoint {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {z : ℂ}
    (hP' : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z)) (gt : ℂ → ℝ) :
    Measurable (affineShiftedJoint hC hcirc z gt) := by
  unfold affineShiftedJoint
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun φ => (hP'.measurable_pairing φ.1 φ.2).add_const _
  · exact measurable_pi_iff.mpr fun p => (hP'.measurable_circle p.1.1 p.1.2 p.2).add_const _

lemma measurable_jointSample_gff {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    Measurable (GFFJointLaw.jointSample hC hcirc) :=
  Measurable.prodMk (measurable_pi_iff.mpr fun φ => hGFF.measurable_pairing φ.1 φ.2)
    (measurable_pi_iff.mpr fun p => hGFF.measurable_circle p.1.1 p.1.2 p.2)

lemma lqgApprox_congr_pos {γ : ℝ} {h h' : ℝ → ℂ → ℝ} (hh : ∀ r z, 0 < r → h r z = h' r z) {ε : ℝ}
    (hε : 0 < ε) : lqgApprox γ h ε = lqgApprox γ h' ε := by
  unfold lqgApprox
  congr 1
  funext z
  rw [hh ε z hε]

lemma isLQGLimit_congr_pos {γ : ℝ} {h h' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hh : ∀ r z, 0 < r → h r z = h' r z) (hm : IsLQGLimit γ h m) : IsLQGLimit γ h' m where
  isLocallyFiniteMeasure := hm.isLocallyFiniteMeasure
  tendsto_integral f hf hfc := by
    refine (hm.tendsto_integral f hf hfc).congr (fun k => ?_)
    rw [lqgApprox_congr_pos hh (dyadicScale_pos k)]

lemma fieldCircleAverage_circleProfile_of_pos (γ : ℝ) (y : C(CircleParameter, ℝ)) (c : ℝ → ℂ → ℝ)
    (hy : ∀ p : CircleParameter, y p = c p.1.1 p.2) (r : ℝ) (z : ℂ) (hr : 0 < r) :
    fieldCircleAverage γ (circleProfile y) r z = fieldCircleAverage γ c r z := by
  rw [ProfileDecoderDerived.fca_circleProfile_eq γ y hr z, fieldCircleAverage, hy]

/-- **Step (iv) of MQ-lh-29 L6.** Almost surely the reference measure `ν ω` is the decoded measure
`Dec(Sel(posPart(hcirc ω)))`: the circle-average profile of `ω` is continuous on positive radii (the
`ae_continuousOn_circle` field of `IsWholePlaneGFF`), `Sel` recovers it, its convergence locus membership follows
from the LQG limit property of `ν ω`, and `IsLQGLimit.unique` identifies the two limits. -/
lemma ae_reference_eq_decoder {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ) (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (hSelRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν : Ω → Measure ℂ) (hν : IsLQGMeasureOfField P γ γ hcirc ν) :
    ∀ᵐ ω ∂P, ν ω = ProfileDecoderDerived.decoder T γ γ (Sel (posPart (hcirc ω))) := by
  have hν' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (ν ω) := hν
  filter_upwards [hν', hGFF.ae_continuousOn_circle] with ω hω hcont
  have hyc : Continuous (fun p : CircleParameter => hcirc ω p.1.1 p.2) := by
    have h1 : Continuous (fun p : CircleParameter => ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h2 : ∀ p : CircleParameter, ((p.1 : ℝ), p.2) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
      fun p => ⟨p.1.2, Set.mem_univ _⟩
    exact hcont.comp_continuous h1 h2
  let y : C(CircleParameter, ℝ) := ⟨fun p => hcirc ω p.1.1 p.2, hyc⟩
  have hSel : Sel (posPart (hcirc ω)) = y := by
    rw [posPart_eq_posExtend]
    exact hSelRec y
  have hmem : y ∈ ProfileDecoderDerived.convSet T γ γ := by
    simp only [ProfileDecoderDerived.convSet, Set.mem_ofPred_eq]
    intro m
    refine ⟨∫ x, T.D m x ∂(ν ω), ?_⟩
    refine (hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport).congr (fun k => ?_)
    unfold ProfileDecoderDerived.approxMeas
    rw [lqgApprox_congr_pos (fun r z hr => fieldCircleAverage_circleProfile_of_pos γ y
      (hcirc ω) (fun p => rfl) r z hr) (dyadicScale_pos k)]
  have hdec : IsLQGLimit γ (fieldCircleAverage γ (circleProfile y))
      (ProfileDecoderDerived.decoder T γ γ y) :=
    ProfileDecoderDerived.isLQGLimit_decoder T γ γ hmem
  have hdec' : IsLQGLimit γ (fieldCircleAverage γ (hcirc ω)) (ProfileDecoderDerived.decoder T γ γ y) :=
    isLQGLimit_congr_pos (fun r z hr => fieldCircleAverage_circleProfile_of_pos γ y
      (hcirc ω) (fun p => rfl) r z hr) hdec
  rw [hSel]
  exact hω.unique hdec'

/-- **Step L6 of MQ-lh-29 (law comparison).** Let `j ≥ 1`, `r = r_j`, and let `gt` be a test function supported in
`B_{2r}(0)` (the output of step L3). For every root `z`, the law of the rooted output `W` (`rootShiftOutput`) is
absolutely continuous with respect to the law of the reference observation `V_j(z, ·)`
(`localReferenceObservation`). Proof: Cameron-Martin reweighting of the affine pullback
`(affinePairing, affineCircle) hC hcirc 1 z` by `gt` (`cameronMartin_profileLaw_map_eq`, with the derived
reweighting `cameronMartinGFFReweighting_derived`), the law identity of the joint samples
(`isWholePlaneGFF_jointLaw_map_eq`), the a.s. identification `ν = Dec(Sel(posPart hcirc))`
(`ae_reference_eq_decoder`), and `P ≪ P'` pushed forward. -/
theorem rootShiftOutput_map_absolutelyContinuous_referenceObservation {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ)) (hSelM : Measurable Sel)
    (hSelRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν : Ω → Measure ℂ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (j : ℕ) (hj : 1 ≤ j) (z : ℂ) (gt : ℂ → ℝ) (hgt : IsTestFunction (ball (0 : ℂ) (2 * localRadius j)) gt) :
    P.map (rootShiftOutput T γ Sel (localRadius j) z hcirc gt) ≪
      P.map (fun ω => localReferenceObservation ν j (z, ω)) := by
  have hr2 : 2 * localRadius j ≤ 1 := by
    have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    unfold localRadius
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  have hgt0 : Real.circleAverage gt 0 1 = 0 := circleAverage_testShift_unit hgt hr2
  -- the reference side (step (iv)): `V_j(z, ·) = rootOutputOfProfile (hcirc ·)` almost surely
  have href := ae_reference_eq_decoder P T γ Sel hSelRec hGFF ν hν
  have hYref : P.map (fun ω => localReferenceObservation ν j (z, ω)) =
      P.map (fun ω => rootOutputOfProfile T γ Sel (localRadius j) z (hcirc ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [href] with ω hω
    simp only [localReferenceObservation, rootOutputOfProfile, hω]
  -- the Cameron-Martin shift of the affine pullback (steps (i)-(ii))
  have hP' : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) :=
    wholePlaneGFFAffineInvariance_derived P hC hcirc hGFF 1 one_ne_zero z
  have hjoint : P.map (GFFJointLaw.jointSample (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z)) =
      P.map (GFFJointLaw.jointSample hC hcirc) :=
    GFFJointLaw.isWholePlaneGFF_jointLaw_map_eq P P _ _ _ _ hP' hGFF
  obtain ⟨P', hac1, hac2, hlaw⟩ :=
    GFFJointLaw.cameronMartin_profileLaw_map_eq S11aj.cameronMartinGFFReweighting_derived P
      (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) hP' gt hgt.1 hgt.2.1 hgt0
  have hlaw' : P'.map (affineShiftedJoint hC hcirc z gt) = P.map (GFFJointLaw.jointSample hC hcirc) :=
    hlaw.trans hjoint
  have hXm := measurable_affineShiftedJoint hP' gt
  have hΨm := measurable_rootOutputOfJoint T γ hSelM (localRadius j) z
  have hJm := measurable_jointSample_gff hGFF
  have hcomp : rootShiftOutput T γ Sel (localRadius j) z hcirc gt =
      rootOutputOfJoint T γ Sel (localRadius j) z ∘ affineShiftedJoint hC hcirc z gt := by
    funext ω
    exact (rootOutputOfProfile_extPos T γ Sel (localRadius j) z
      (fun s x => affineCircle hcirc 1 z ω s x + Real.circleAverage gt x s)).symm
  have hPW' : P'.map (rootShiftOutput T γ Sel (localRadius j) z hcirc gt) =
      P.map (fun ω => rootOutputOfProfile T γ Sel (localRadius j) z (hcirc ω)) := by
    have hfun : rootOutputOfJoint T γ Sel (localRadius j) z ∘ GFFJointLaw.jointSample hC hcirc =
        fun ω => rootOutputOfProfile T γ Sel (localRadius j) z (hcirc ω) := by
      funext ω
      exact rootOutputOfProfile_extPos T γ Sel (localRadius j) z (hcirc ω)
    rw [hcomp, ← Measure.map_map hΨm hXm, hlaw', Measure.map_map hΨm hJm, hfun]
  have hW := measurable_rootShiftOutput T γ hSelM hGFF (localRadius j) z gt
  have hPW : P.map (rootShiftOutput T γ Sel (localRadius j) z hcirc gt) ≪
      P'.map (rootShiftOutput T γ Sel (localRadius j) z hcirc gt) :=
    hac2.map hW
  rw [hPW', ← hYref] at hPW
  exact hPW

end RootedShiftedNullTransferLaw

end HarmonicBalls
