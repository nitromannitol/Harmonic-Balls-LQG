import HarmonicBalls.Proofs.Sec6.SizeRatioScalingLaw

/-! # Scaling of relative annular collar events

The LQG scale-law statement below uses the affine and coordinate-change
inputs. It concerns a fixed centre and does not assert a rooted law.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

/-- Failure of a relative mass bound for the two-sided collar of the annulus
with radii three and five times the scale. -/
def RelativeCollarFailure (μ : Measure ℂ) (r η : ℝ) (d : ℝ≥0∞) : Prop :=
  d * μ (annulus 0 (3*r) (5*r)) <
    μ (annulus 0 (3*r-η*r) (5*r+η*r) \ annulus 0 (3*r+η*r) (5*r-η*r))

/-- The relative collar failure event is measurable in the measure. -/
theorem measurableSet_relativeCollarFailure (r η : ℝ) (d : ℝ≥0∞) :
    MeasurableSet {μ : Measure ℂ | RelativeCollarFailure μ r η d} := by
  apply measurableSet_lt
  · exact measurable_const.mul (Measure.measurable_coe
      (isOpen_ball.measurableSet.diff measurableSet_closedBall))
  · exact Measure.measurable_coe ((isOpen_ball.measurableSet.diff measurableSet_closedBall).diff
      (isOpen_ball.measurableSet.diff measurableSet_closedBall))

/-- Multiplication by a finite positive mass factor preserves relative
collar failure. -/
theorem relativeCollarFailure_smul (μ : Measure ℂ) (r η : ℝ) (d t : ℝ≥0∞)
    (ht : t ≠ 0) (htop : t ≠ ∞) :
    RelativeCollarFailure (t • μ) r η d ↔ RelativeCollarFailure μ r η d := by
  unfold RelativeCollarFailure
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [show d * (t * μ (annulus 0 (3*r) (5*r))) =
    (d * μ (annulus 0 (3*r) (5*r))) * t by ac_rfl,
    mul_comm t, ENNReal.mul_lt_mul_iff_left ht htop]

/-- Spatial dilation transports the relative collar event to the
correspondingly dilated scale. -/
theorem relativeCollarFailure_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (r η : ℝ) (d : ℝ≥0∞) :
    RelativeCollarFailure (μ.map (fun x : ℂ => k⁻¹ • x)) r η d ↔
      RelativeCollarFailure μ (k*r) η d := by
  have hm (A : Set ℂ) (hA : MeasurableSet A) :
      (μ.map (fun x : ℂ => k⁻¹ • x)) A = μ ((fun x : ℂ => k⁻¹ • x) ⁻¹' A) :=
    Measure.map_apply (by fun_prop) hA
  have ha (s t : ℝ) : (fun x : ℂ => k⁻¹ • x) ⁻¹' annulus 0 s t =
      annulus 0 (k*s) (k*t) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
  have hann (s t : ℝ) : MeasurableSet (annulus (0 : ℂ) s t) :=
    isOpen_ball.measurableSet.diff measurableSet_closedBall
  unfold RelativeCollarFailure
  rw [hm _ (hann _ _), hm _ ((hann _ _).diff (hann _ _)), preimage_sdiff, ha, ha, ha]
  ring_nf

/-- The centred failure probability is independent of positive scale under
the GFF affine and LQG coordinate-change laws. -/
theorem measure_relativeCollarFailure_scale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    {r : ℝ} (hr : 0 < r) (η : ℝ) (d : ℝ≥0∞) :
    P {ω | RelativeCollarFailure (μ ω) 1 η d} =
      P {ω | RelativeCollarFailure (μ ω) r η d} := by
  have hd := h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hr
  have heq := hd.measure_mem_eq (measurableSet_relativeCollarFailure 1 η d)
  have htransport (ω : Ω) :
      RelativeCollarFailure (normalizedPullbackMeasure γ α r (hcirc ω) (μ ω)) 1 η d ↔
        RelativeCollarFailure (μ ω) r η d := by
    unfold normalizedPullbackMeasure
    rw [relativeCollarFailure_smul _ _ _ _ _ (by positivity) ENNReal.ofReal_ne_top,
      relativeCollarFailure_map_inv_smul _ hr]
    simp only [mul_one]
  have hs : (fun ω => normalizedPullbackMeasure γ α r (hcirc ω) (μ ω)) ⁻¹'
      {ν | RelativeCollarFailure ν 1 η d} = {ω | RelativeCollarFailure (μ ω) r η d} := by
    ext ω
    exact htransport ω
  rw [hs] at heq
  exact heq

end HarmonicBalls.Section6
