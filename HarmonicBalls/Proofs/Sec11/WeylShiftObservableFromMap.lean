import HarmonicBalls.Proofs.Sec11.CanonicalMetricMeasureObservable
import HarmonicBalls.Proofs.Sec11.PinchShiftLaw
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Metric-measure observable under a sample-space shift

The field shift and its metric identity remain explicit. The measure Weyl
identity is obtained from the LQG construction, and the singular metric-field
axioms are staged pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- A quasi-measure-preserving shift implementing the circle-average and
metric shifts induces an absolutely continuous law for any fixed canonical
observable. No separate measurable modification of the shifted metric is
required. -/
theorem canonicalWeylShiftObservable_of_shiftMap
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {f : ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hf : Continuous f)
    (X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d})
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω)
    (τ : Ω → Ω) (hτ : Measure.QuasiMeasurePreserving τ P P)
    (hc : ∀ᵐ ω ∂P, fieldCircleAverage α (hcirc (τ ω)) =
      addCircleAverage (fieldCircleAverage α (hcirc ω)) f)
    (hd : ∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal) :
    ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
      AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
      (∀ᵐ ω ∂P, (Y ω).1 =
          (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
        (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  have hm := ae_lqgMeasure_comp_eq_withDensity_of_circleAverage_shift
    P γ α hC hcirc μ f τ (Section6.lqgMeasureWeylScaling Ω P γ α hC hcirc)
    hgff hγ hγ₂ hα hμ hf hτ hc
  have hXmap : AEMeasurable X (P.map τ) := hX.mono_ac hτ.absolutelyContinuous
  refine ⟨X ∘ τ, hXmap.comp_aemeasurable hτ.aemeasurable, ?_, ?_⟩
  · rw [← AEMeasurable.map_map_of_aemeasurable hXmap hτ.aemeasurable]
    have hleft : (P.map τ).map (hX.mk X) = (P.map τ).map X :=
      Measure.map_congr ((hX.ae_eq_mk.filter_mono hτ.absolutelyContinuous.ae_le).symm)
    have hright : P.map (hX.mk X) = P.map X := Measure.map_congr hX.ae_eq_mk.symm
    simpa only [hleft, hright] using hτ.absolutelyContinuous.map hX.measurable_mk
  · filter_upwards [hτ.ae hdecode, hm, hd] with ω hdec hmeasure hmetric
    exact ⟨hdec.1.trans hmeasure, hdec.2.trans hmetric⟩

/-- The staged singular metric-field axioms construct the canonical observable;
a compatible sample-space shift then supplies its shifted joint law. -/
theorem exists_canonicalWeylShiftObservable_of_shiftMap
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ} {f : ℂ → ℝ}
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hf : Continuous f)
    (τ : Ω → Ω) (hτ : Measure.QuasiMeasurePreserving τ P P)
    (hc : ∀ᵐ ω ∂P, fieldCircleAverage α (hcirc (τ ω)) =
      addCircleAverage (fieldCircleAverage α (hcirc ω)) f)
    (hd : ∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal) :
    ∃ X Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
      AEMeasurable X P ∧ AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
      (∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω) ∧
      (∀ᵐ ω ∂P, (Y ω).1 =
          (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
        (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  obtain ⟨X, hX, hdecode⟩ := exists_canonicalMetricMeasureObservable_of_metricFieldAxioms
    haxioms hgff hγ hγ₂ hα hD hμ
  obtain ⟨Y, hY, hac, hYdecode⟩ := canonicalWeylShiftObservable_of_shiftMap
    hgff hγ hγ₂ hα hμ hf X hX hdecode τ hτ hc hd
  exact ⟨X, Y, hX, hY, hac, hdecode, hYdecode⟩


end HarmonicBalls
