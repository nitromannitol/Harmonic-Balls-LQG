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

end RootedShiftedNullTransferLaw

end HarmonicBalls
