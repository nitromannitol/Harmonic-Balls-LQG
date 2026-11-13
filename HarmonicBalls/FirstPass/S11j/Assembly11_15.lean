import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.FirstPass.S11j.ThresholdsAE
import HarmonicBalls.FirstPass.S11j.InnerMeasure
import HarmonicBalls.FirstPass.S11j.PositiveWeylFinite
import HarmonicBalls.FirstPass.S11j.PositiveWeylBump
import HarmonicBalls.FirstPass.S11j.PositiveWeylInverse
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# Section 11: conditional assembly of the faithful Lemma 11.15

Conditional assembly, kept separate from `firstPass_11_15_corrected`. For one fixed buffered geometry, one insertion
`α₀ < Q`, one exponent `ξ > 0` and one LQG metric of a whole-plane GFF, it proves the positive-measure conclusion of
corrected Lemma 11.15 (`pinchFirstEvent`, paper lines 3347-3349, 3659-3696) from:

* the Cameron-Martin event transfer `CameronMartinMetricEventTransferMeasurableFrozen` (`FirstPass/Frozen/S11j.lean:37`,
  EXTERNAL, truth check pending);
* the named measurability and positivity inputs (M1)-(M3) below (paper line 3664-3667 asserts that the four variables
  are positive and finite; measurability is not proven in the paper).

**Status: hM11 is unsatisfiable whenever the event is nonempty, so this conditional is vacuous as it
stands and is not a proof of the faithful 11.15.** `pinchFirstEvent` takes suprema, infima and path infima over
uncountable index sets. A set of metrics in the product σ-algebra is determined by countably many coordinates. If
`d` satisfies the event and `(a, b) ∈ Q' × frontier Q` is outside those coordinates, then changing `d a b` to `-1`
makes `setDist ≤ 0`, so the first conjunct fails. The transfer needs measurability for the canonical field law
instead.

Route (paper 3659-3696): thresholds `n, k, m, l` with positive probability for the base metric `D`; a positive
smooth shift `f` from `exists_uniform_first_event_shift` (the event holds for the shifted metric `e^{ξ f} D` on the
thresholds event); the Cameron-Martin transfer returns the event to the unshifted metric; the inner measure gives a
measurable subset. The positive singular-field identities (length metric, finiteness, inverse) are proven in
`PositiveWeylBump` and `PositiveWeylInverse`.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Conditional 11.15: the positive-measure conclusion of corrected Lemma 11.15 for one geometry, one field and one
insertion, given the named inputs (M1)-(M3) and the Cameron-Martin transfer. -/
theorem pinchFirstEvent_positive_of_inputs
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ)
    {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ) (hξ : 0 < ξ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hCM : CameronMartinMetricEventTransferMeasurableFrozen.{u})
    -- (M1) the four threshold variables of the base metric are almost everywhere measurable
    (hM1 : AEMeasurable (fun ω => ENNReal.ofReal (setDist (D ω) Q' (frontier Q))) P)
    (hM2 : AEMeasurable (fun ω => ⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric (D ω) (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) P)
    (hM3 : AEMeasurable (fun ω => ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2)))) P)
    (hM4 : AEMeasurable (fun ω => internalDiam (D ω) δ (T \ thickening (3 * δ) W)) P)
    -- (M2) positivity and finiteness of the four variables (paper line 3664-3667)
    (hM5 : ∀ᵐ ω ∂P, 0 < ENNReal.ofReal (setDist (D ω) Q' (frontier Q)))
    (hM6 : ∀ᵐ ω ∂P, (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric (D ω) (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < ∞)
    (hM7 : ∀ᵐ ω ∂P, 0 < ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))))
    (hM8 : ∀ᵐ ω ∂P, internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ∞)
    -- (M3) null measurability of the events: of the unshifted metric, and of every admissible Weyl shift
    (hM9 : NullMeasurableSet {ω | pinchFirstEvent (D ω) W T Q' Q δ} P)
    (hM10 : ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
      NullMeasurableSet {ω | pinchFirstEvent (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ} P)
    -- (M11, named M4 in the notes) the event, as a predicate on metrics, is measurable in the product σ-algebra. This is
    -- required by the corrected Cameron-Martin transfer, but it is FALSE for every nonempty event (see the status above).
    (hM11 : MeasurableSet {d : ℂ → ℂ → ℝ | pinchFirstEvent d W T Q' Q δ}) :
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A := by
  have hξ0 : 0 ≤ ξ := hξ.le
  -- the shift of the core lemma
  have hconf := h.toPinchPointProofConfiguration h.U_nonempty
  obtain ⟨n, k, m, l, hn, hk, hG⟩ :=
    exists_thresholds_measure_pos_of_aemeasurable hM1 hM2 hM3 hM4 hM5 hM6 hM7 hM8
  obtain ⟨f, hsm, hcomp, hnonneg, hsupp, hcore⟩ :=
    hconf.exists_uniform_first_event_shift hξ n m k l hn hk
  -- the shift vanishes on the unit circle: `Q` lies in `4 < |z| < 5` and `δ < 10⁻³`
  have hcirc1 : ∀ z : ℂ, ‖z‖ = 1 → f z = 0 := by
    intro z hz
    apply hsupp z
    rintro (hzQ | hz0)
    · obtain ⟨q, hq, hdist⟩ := mem_thickening_iff.mp hzQ
      have hqa := h.closure_Q_subset (subset_closure hq)
      have hq4 : 4 < ‖q‖ := by
        have hqa' := hqa.1
        simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hqa'
        rw [dist_zero_right] at hqa'
        exact hqa'.2
      have hqz : ‖q - z‖ < δ := by
        rw [dist_comm, dist_eq_norm] at hdist
        exact hdist
      have htri := norm_sub_norm_le q z
      linarith [h.delta_lt, h.delta_pos]
    · have hz1 : ‖z‖ < δ := mem_ball_zero_iff.mp hz0
      linarith [h.delta_lt, h.delta_pos]
  -- almost surely: the Weyl-shifted metric is a length metric with the identities of the core lemma
  have ae1 := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  have ae2 := ae_singularField_nonneg_weylBump_lengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD hξ0
  have ae3 := ae_singularField_bounded_weylScaling_finite P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD hξ0
  have ae4 := ae_singularField_nonneg_weylBump_inverse_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD hξ0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z, f z ≤ M := by
    obtain ⟨c, hc⟩ :=
      exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hsm.continuous.neg hcomp.neg
    exact ⟨-c, fun z => by
      have h' : c ≤ -f z := hc z
      linarith⟩
  -- on the thresholds event, the core lemma gives the event for the shifted metric
  have hsub : ∀ᵐ ω ∂P,
      ω ∈ {ω | (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))) ∧
        internalDiam (D ω) δ (T \ thickening (3 * δ) W) ≤ (l : ℝ≥0∞)} →
      ω ∈ {ω | pinchFirstEvent (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ} := by
    filter_upwards [ae1, ae2, ae3, ae4] with ω e1 e2 e3 e4 hthr
    obtain ⟨t1, t2, t3, t4⟩ := hthr
    exact hcore (D ω) (fun x y => (weylScaling (D ω) ξ f x y).toReal) e1
      (e2 f hsm.continuous hcomp hnonneg) (fun x y => ENNReal.toReal_nonneg)
      (fun x y => (e3 f M hM x y).2) (e4 f hsm.continuous hcomp hnonneg) t1 t2 t3 t4
  -- the thresholds event has positive probability, so does the shifted event
  have hpos1 : 0 < P {ω | pinchFirstEvent (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ} :=
    lt_of_lt_of_le hG (measure_mono_ae hsub)
  -- Cameron-Martin transfer back to the unshifted metric, then the inner measure
  have hpos2 : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ} :=
    hCM γ α₀ ξ f hγ hγ₂ hα hsm hcomp hcirc1 Ω P hC hcirc D (fun M => pinchFirstEvent M W T Q' Q δ)
      hM11 hgff hD (hM10 f hsm hcomp hcirc1) hM9 hpos1
  exact exists_measurable_subset_pos_of_nullMeasurableSet hM9 hpos2

end HarmonicBalls
