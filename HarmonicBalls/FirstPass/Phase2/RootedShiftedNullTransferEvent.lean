import HarmonicBalls.FirstPass.Phase2.B2ShiftedProfileDecoder2
import HarmonicBalls.FirstPass.Phase2.RootedDominationJoint
import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmDMSConstant

/-! # Probability-one event of the shifted-root null transfer (MQ-lh-29, items (a), (b), (c))

Items (a), (b) and (c) of the probability-one event `E_z` of `notes/fp-gaps/MATH-ANSWERS.md`, section `## MQ-lh-29`
(lines 769-780), for a whole-plane GFF `hcirc` under a probability measure `P`:

* (a) `hcirc ω 1 0 = 0` almost surely: the circle average of the field at radius `1` about `0` vanishes
  (`IsWholePlaneGFF.ae_circleAverage_one_zero`). Consequently the DMS constant `dmsConstant γ z (hcirc ω 1 0)` vanishes
  for `‖z‖ ≤ 1` (`dmsConstant_ae_zero`, the L1 step).
* (b) the circle-average profile `(r, x) ↦ hcirc ω r x` is continuous on `(0, ∞) × ℂ` almost surely
  (`IsWholePlaneGFF.ae_continuousOn_circle`); this is the input of the canonical selector.
* (c) for Lebesgue-a.e. root `z` in `localDomain j`, almost surely every continuous profile `y` whose zero extension is the
  positive part of the DMS-shifted circle profile lies in the convergence locus `convSet T γ a0`. Route: the producer
  `shifted_rootedLQGMeasure_ae_exists` (`B2ShiftedProfileDecoder2.lean`, from `ae_exists_rootedLQGMeasure_derived`) gives,
  for a.e. `z`, an LQG measure of `rootedCircleFieldP a0 γ hcirc z`; the identity
  `rootedCircleFieldP a0 γ hcirc z ω = fieldCircleAverage a0 (dmsShiftedCircle γ z (hcirc ω))` holds once the DMS constant
  vanishes; the dyadic-scale comparison `isLQGLimit_congr_of_pos` transfers the LQG limit to `y`; and the convergence
  membership is read off from the LQG limit, as in the proof of `lqgMeasureOfProfileMeasurable_derived`.

The joint identity `DMSLemmaA10WholePlaneMarkedJointPosStmt` (candidate, pending truth check) is not used: this route is the
`α₀`-version of step 5 and needs only the marked input `DMSLemmaA10WholePlaneMarked`, as the producer does.

Terminology: Duplantier-Sheffield (LQG measures of the GFF), Armitage-Gardiner (circle averages).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
open FirstPassS11atProducers

namespace HarmonicBalls

universe u

/-- **(a)** Almost surely the circle average of the whole-plane field at radius `1` about `0` vanishes. -/
theorem ae_circleAverage_one_zero_event {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 :=
  hGFF.ae_circleAverage_one_zero

/-- **(b)** Almost surely the circle-average profile is continuous on the positive radii. -/
theorem ae_continuousOn_circleProfile_event {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) :=
  hGFF.ae_continuousOn_circle

/-- A continuous profile `y` whose zero extension is the positive part of the DMS-shifted circle profile takes the
values of that shifted profile at every positive radius. -/
theorem circleProfile_eq_dmsShifted_of_posExtend {γ : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ} {y : C(CircleParameter, ℝ)}
    (hy : posPart (dmsShiftedCircle γ z hc) = posExtend ⇑y) {r : ℝ} (hr : 0 < r) (x : ℂ) :
    circleProfile y r x = dmsShiftedCircle γ z hc r x := by
  have hF : ∀ p : CircleParameter, y p = posPart (dmsShiftedCircle γ z hc) p.1 p.2 := by
    rintro ⟨⟨s, hs⟩, w⟩
    have hs' : 0 < s := hs
    have h := congrFun (congrFun hy s) w
    simp only [posExtend, hs', ↓reduceDIte] at h
    exact h.symm
  rw [FirstPassS11atProducers.circleProfile_eq_of_pos (g := posPart (dmsShiftedCircle γ z hc)) hF hr x]
  simp [posPart, hr]

/-- **(c) on the unit ball.** For Lebesgue-a.e. root `z` in the unit ball, almost surely every continuous profile `y`
whose zero extension is the positive part of the DMS-shifted circle profile lies in `convSet T γ a0`. -/
theorem ae_shifted_mem_convSet_ball {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ProfileDecoderDerived.TestFamily) (γ a0 : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : a0 < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ a0 hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P, ∀ y : C(CircleParameter, ℝ),
      posPart (dmsShiftedCircle γ z (hcirc ω)) = posExtend ⇑y →
        y ∈ ProfileDecoderDerived.convSet T γ a0 := by
  filter_upwards [shifted_rootedLQGMeasure_ae_exists P γ a0 hC hcirc 0 1 hGFF hγ0 hγ2 hα hExist0 hExistα hA10
      subset_rfl, ae_restrict_mem measurableSet_ball] with z hz hzb
  obtain ⟨μz, hμz⟩ := hz
  have hμz' : ∀ᵐ ω ∂P, IsLQGLimit γ (rootedCircleFieldP a0 γ hcirc z ω) (μz ω) := hμz
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hzb).le
  filter_upwards [hμz', dmsConstant_ae_zero hGFF γ hz1] with ω hμω hκ
  intro y hy
  have hf : (fun w : ℂ => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) = dmsShift γ z := by
    funext w
    unfold dmsShift
    rw [max_comm]
  have key : ∀ (r : ℝ) (x : ℂ), rootedCircleFieldP a0 γ hcirc z ω r x =
      fieldCircleAverage a0 (dmsShiftedCircle γ z (hcirc ω)) r x := by
    intro r x
    simp only [rootedCircleFieldP, addCircleAverage, fieldCircleAverage, dmsShiftedCircle, hκ, add_zero, hf]
    ring
  have heq : ∀ (k : ℕ) (x : ℂ), rootedCircleFieldP a0 γ hcirc z ω (dyadicScale k) x =
      fieldCircleAverage a0 (circleProfile y) (dyadicScale k) x := by
    intro k x
    have hr : 0 < dyadicScale k := by unfold dyadicScale; positivity
    rw [key]
    simp only [fieldCircleAverage]
    rw [circleProfile_eq_dmsShifted_of_posExtend hy hr x]
  have hcon := isLQGLimit_congr_of_pos (hε := rootedCircleFieldP a0 γ hcirc z ω) heq hμω
  intro m
  exact ⟨_, hcon.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport⟩

/-- **The probability-one event `E_z` (items (a), (b), (c)).** For Lebesgue-a.e. root `z` in `localDomain j`, almost
surely: `hcirc ω 1 0 = 0`; `hcirc ω` is continuous on positive radii; and every continuous profile equal to the positive
part of the DMS-shifted circle profile lies in `convSet T γ a0`. -/
theorem ae_rootedShiftedNullEvent {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ProfileDecoderDerived.TestFamily) (γ a0 : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : a0 < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ a0 hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ) (j : ℕ) :
    ∀ᵐ z ∂(volume.restrict (localDomain j)), ∀ᵐ ω ∂P,
      hcirc ω 1 0 = 0 ∧ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        ∀ y : C(CircleParameter, ℝ), posPart (dmsShiftedCircle γ z (hcirc ω)) = posExtend ⇑y →
          y ∈ ProfileDecoderDerived.convSet T γ a0 := by
  have hdom : localDomain j ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rcases hz with ⟨-, h2⟩
    have h0 : 0 ≤ localRadius j := by unfold localRadius; positivity
    rw [mem_ball_zero_iff]
    linarith
  have hab : ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 ∧ ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) :=
    (ae_circleAverage_one_zero_event hGFF).and (ae_continuousOn_circleProfile_event hGFF)
  have hc := ae_shifted_mem_convSet_ball P T γ a0 hγ0 hγ2 hα hC hcirc hGFF hExist0 hExistα hA10
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hdom hc] with z hz
  filter_upwards [hz, hab] with ω h1 h2
  exact ⟨h2.1, h2.2, h1⟩

end HarmonicBalls
