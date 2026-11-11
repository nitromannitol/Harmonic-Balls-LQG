import HarmonicBalls.FirstPass.S11h.PairPersistence11_17
import HarmonicBalls.Steps.Sec11.MetricField
import HarmonicBalls.Steps.Sec11.SingularWeylBumpLength

/-!
# Lemma 11.17, Step 17.5 (almost-sure part): admissibility of the bump shift

The almost-sure hypotheses `hD`, `hE`, `hfin` of `pinchEvents_of_bumpShift` (PairPersistence11_17.lean), obtained
for every nonpositive weight at once, so that the probabilistic step of Lemma 11.17 may use them uniformly in the
bump `φ` and in `k ∈ (0, 1]`. The only input is the staged metric field axiom `LQGMetricFieldAxioms` (Proposed/LQG.lean,
Fact 2.2 I-IV, pending operator source-check), taken as an explicit hypothesis. The three almost-sure facts are the
Steps lemmas `ae_isEuclideanLengthMetric_of_metricFieldAxioms` (Steps/Sec11/MetricField.lean),
`ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms` (Steps/Sec11/SingularWeylBumpLength.lean) and
`ae_singularField_negative_weylScaling_finite` (Steps/Sec11/SingularFieldWeylForward.lean).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Almost surely, the metric `D` is a Euclidean length metric, the Weyl scaling `e^{ξ f} · D` by every continuous
compactly supported nonpositive weight `f` is a Euclidean length metric (`bumpShiftedMetric`), and the Weyl scaling by
every nonpositive weight is finite. -/
theorem ae_bumpShift_admissible {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧
      (∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
        IsEuclideanLengthMetric (bumpShiftedMetric (D ω) ξ f)) ∧
      (∀ f : ℂ → ℝ, (∀ z, f z ≤ 0) → ∀ x y, weylScaling (D ω) ξ f x y ≠ ⊤) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ] with ω h1 h2 h3
  exact ⟨h1, fun f hc hk hf => h2 f hc hk hf, fun f hf x y => (h3 f hf x y).1.ne⟩

/-- Almost surely, for every continuous compactly supported bump `φ` of the paper's geometry (`IsBufferedPinchGeometry`)
and every `k ∈ (0, 1]`, the bump lowering `f = ξ⁻¹ log k · φ` carries the first and second pinch events of `D ω`
(together with the strict inequality `k · diam < D(∂B_{2δ}, ∂B_{3δ})`) to the three pinch events of the shifted pair.
The exceptional null set does not depend on `φ` or on `k`. -/
theorem ae_pinchEvents_bumpShift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (hξ : 0 < ξ)
    {U V W T Q' Q : Set ℂ} {δ M k : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφcs : HasCompactSupport φ)
    (hφsupp : ∀ z, z ∉ thickening (5 * δ) W → φ z = 0)
    (hφO2 : ∀ z ∈ closure (pinchO2 δ V W), φ z = 1) (hφU : ∀ z ∈ closure U, φ z = 0)
    (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    ∀ᵐ ω ∂P,
      (pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M ∧
        ENNReal.ofReal k * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
          ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) →
      (pinchFirstEvent (bumpShiftedMetric (D ω) ξ (bumpExponent ξ k φ)) W T Q' Q δ ∧
        pinchSecondEvent ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * bumpExponent ξ k φ x))))
          (bumpShiftedMetric (D ω) ξ (bumpExponent ξ k φ)) U V δ M ∧
        pinchThirdEvent (bumpShiftedMetric (D ω) ξ (bumpExponent ξ k φ)) V W δ) := by
  have hneg : ∀ z, bumpExponent ξ k φ z ≤ 0 := by
    intro z
    unfold bumpExponent
    have hl : Real.log k ≤ 0 := Real.log_nonpos hk0.le hk1
    have hi : 0 < ξ⁻¹ := inv_pos.2 hξ
    have h2 : ξ⁻¹ * Real.log k ≤ 0 := by nlinarith
    have h3 := mul_nonneg (neg_nonneg.mpr h2) (hφ01 z).1
    nlinarith
  have hcont : Continuous (bumpExponent ξ k φ) := by
    unfold bumpExponent
    exact continuous_const.mul hφc
  have hcs : HasCompactSupport (bumpExponent ξ k φ) := by
    unfold bumpExponent
    exact hφcs.mul_left
  filter_upwards [ae_bumpShift_admissible P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hξ.le] with ω hω
  rintro ⟨hE1, hE2, hstrict⟩
  exact pinchEvents_of_bumpShift h hφc hφsupp hφO2 hφU hφ01 hξ hk0 hk1 hω.1
    (fun x y => hω.2.2 _ hneg x y) (hω.2.1 _ hcont hcs hneg) hE1 hE2 hstrict

end HarmonicBalls

#print axioms HarmonicBalls.ae_bumpShift_admissible
#print axioms HarmonicBalls.ae_pinchEvents_bumpShift
