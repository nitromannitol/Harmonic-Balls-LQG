import HarmonicBalls.FirstPass.S11c.JointVersion
import HarmonicBalls.FirstPass.S11c.Event

/-!
# Proposition 11.7, measurability of the scale event `coneMassEvent`

For a cone `Q`, a constant `c`, a scale `r` and a point `z`, the set of realisations `ω` at
which the scale event `coneMassEvent (μ ω) Q c r z` (`HarmonicBalls/Draft/Section11.lean:72`) holds is null-measurable, when
`μ` is the LQG measure of the field and the jointly measurable version of `JointVersion.lean` is available. The event is
`ofReal c * annulusGreenPotentialSup (μ ω) z (3r) (6r) ≤ μ ω (annulus z r (2r) ∩ coneAt Q z)`, and both sides are
almost surely measurable by `JointVersion.lean`. This is the measurability of the event in Lemma 11.7 (paper
`lemma:mu_h-bad-and-harnack`, corrected paper line 2896).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The open-minus-closed annulus is Borel. -/
theorem measurableSet_annulus_scale (z : ℂ) (r₁ r₂ : ℝ) : MeasurableSet (annulus z r₁ r₂) :=
  (isOpen_ball.sdiff isClosed_closedBall).measurableSet

/-- The scale event `coneMassEvent (μ ω) Q c r z` is null-measurable in `ω`. -/
theorem nullMeasurableSet_coneMassEvent_of_joint_version {P : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {M : Ω × ℝ → Measure ℂ} (hM : Measurable M)
    (hMlim : ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α)))
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hα₀ : α₀ < lqgQ γ) {Q : Set ℂ} (hQ : IsCone Q)
    (c r : ℝ) (z : ℂ) :
    NullMeasurableSet {ω | coneMassEvent (μ ω) Q c r z} P := by
  obtain ⟨Y, hY, hYeq⟩ :=
    exists_measurable_annulusGreenPotentialSup_of_joint_version hM hMlim hμ hα₀ z (3 * r) (6 * r)
  have hL : AEMeasurable (fun ω => ENNReal.ofReal c * annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r)) P := by
    have hY' : Measurable fun ω => ENNReal.ofReal c * Y ω := measurable_const.mul hY
    refine hY'.aemeasurable.congr ?_
    filter_upwards [hYeq] with ω hω
    rw [hω]
  have hR : AEMeasurable (fun ω => μ ω (annulus z r (2 * r) ∩ coneAt Q z)) P :=
    aemeasurable_mass_of_joint_version hM hMlim hμ hα₀ _
      ((measurableSet_annulus_scale z r (2 * r)).inter (measurableSet_coneAt hQ z))
  exact nullMeasurableSet_le hL hR

end HarmonicBalls.S11c
