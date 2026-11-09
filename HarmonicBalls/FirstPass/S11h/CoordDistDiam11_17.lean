import HarmonicBalls.FirstPass.S11h.CertScalars11_17
import HarmonicBalls.FirstPass.S11j.CertificateE1
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11h.OuterDiamFinite

/-!
# First pass, Lemma 11.17: the set-distance and internal-diameter coordinates (fp-S11h, owner n2)

Coordinates 1-5, 8 and 9 of `pinchScalars` are set distances and internal diameters of the pair. Each has a countable
formula over internal metrics of open sets: `ofReal_setDist_eq_countable` (open set `univ`) and
`internalDiam_eq_countable` (open set `thickening δ A`). The frozen field decoder
`LQGInternalMetricWeylAeMeasurableFrozen` (Frozen/S11d.lean:111) gives, for each open `W` and each pair of points, a measurable
functional of the field. Countable infima and suprema of measurable functionals are measurable, so each coordinate has a
field-level version, almost surely equal to the coordinate of the shifted field `h^ℂ + g` for every continuous `g`
(the measure-free part of the certificate; the identification of `fieldMetric (addFunPairing (hC ω) g)` with the Weyl
shifted pair is Step K5 of the route, not here).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The real metric of the field `h^ℂ + g - α₀ log|·|`: the Weyl scaling of `𝔇(T)` by `-α₀ log|·|`, as in the decoder
`LQGInternalMetricWeylAeMeasurableFrozen` and in `IsLQGMetricOfField`. -/
noncomputable def fieldMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α₀ : ℝ) (T : (ℂ → ℝ) → ℝ) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 T) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal

/-- Almost surely the metric of the pair is the field metric of `hC ω` (from the defining relation of
`IsLQGMetricOfField`, with `ENNReal.toReal_ofReal`). -/
theorem ae_eq_fieldMetric {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun z => -α₀ * Real.log ‖z‖) u v) :
    ∀ᵐ ω ∂P, D ω = fieldMetric 𝔇 ξ α₀ (hC ω) := by
  filter_upwards [hD] with ω hω
  funext u v
  simp only [fieldMetric]
  rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]

/-- Set distance coordinate (coordinates 1, 3, 5, 9 of `pinchScalars`): a single measurable field functional `Φ` whose
almost sure value at `h^ℂ + g` is `ofReal (setDist D A B)` for the field metric `D` of `h^ℂ + g`, for every continuous `g`
whose field metric is a Euclidean length metric almost surely. Source of the countable formula:
`ofReal_setDist_eq_countable` (CertificateE1.lean:52) with `W = univ` in the decoder. -/
theorem exists_field_ofReal_setDist (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ ξ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (A B A' B' : Set ℂ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAA : A' ⊆ A) (hBB : B' ⊆ B) (hAc : A ⊆ closure A') (hBc : B ⊆ closure B')
    (hA'c : A'.Countable) (hB'c : B'.Countable) :
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
        ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) =
          ENNReal.ofReal (setDist (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) A B) := by
  have : Countable A' := hA'c.to_subtype
  have : Countable B' := hB'c.to_subtype
  choose Φ hΦm hΦeq using fun p : ℂ × ℂ =>
    hdec γ ξ α₀ Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hα h𝔇 univ isOpen_univ p.1 p.2
  refine ⟨fun T => ⨅ a : A', ⨅ b : B', Φ (a.1, b.1) T, ?_, ?_⟩
  · exact Measurable.iInf fun a => Measurable.iInf fun b => hΦm (a.1, b.1)
  intro g hg hE
  have hae : ∀ᵐ ω ∂P, ∀ a : A', ∀ b : B', Φ (a.1, b.1) (addFunPairing (hC ω) g) =
      internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) univ a.1 b.1 := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    exact hΦeq (a.1, b.1) g hg
  filter_upwards [hae, hE] with ω hω hEω
  show ⨅ a : A', ⨅ b : B', Φ (a.1, b.1) (addFunPairing (hC ω) g) = _
  simp only [hω]
  rw [ofReal_setDist_eq_countable hEω hA hB hAA hBB hAc hBc]
  simp only [iInf_subtype']

/-- Internal diameter coordinate (coordinates 2, 4, 8 of `pinchScalars`): a single measurable field functional `Φ` whose
almost sure value at `h^ℂ + g` is `internalDiam δ A` for the field metric of `h^ℂ + g`, for every continuous `g` whose
field metric is a Euclidean length metric almost surely. Source of the countable formula: `internalDiam_eq_countable`
(CertificateE1.lean:63), with the decoder on the open set `thickening δ A`. -/
theorem exists_field_internalDiam (hdec : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ ξ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (δ : ℝ) (hδ : 0 < δ) (A A' : Set ℂ) (hAA : A' ⊆ A) (hAc : A ⊆ closure A')
    (hA'c : A'.Countable) :
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
        ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) =
          internalDiam (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) δ A := by
  have : Countable A' := hA'c.to_subtype
  choose Φ hΦm hΦeq using fun p : ℂ × ℂ =>
    hdec γ ξ α₀ Ω P hC hcirc 𝔇 hGFF hγ0 hγ2 hα h𝔇 (thickening δ A) isOpen_thickening p.1 p.2
  refine ⟨fun T => ⨆ x : A', ⨆ y : A', Φ (x.1, y.1) T, ?_, ?_⟩
  · exact Measurable.iSup fun x => Measurable.iSup fun y => hΦm (x.1, y.1)
  intro g hg hE
  have hae : ∀ᵐ ω ∂P, ∀ x : A', ∀ y : A', Φ (x.1, y.1) (addFunPairing (hC ω) g) =
      internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) (thickening δ A) x.1 y.1 := by
    rw [ae_all_iff]
    intro x
    rw [ae_all_iff]
    intro y
    exact hΦeq (x.1, y.1) g hg
  filter_upwards [hae, hE] with ω hω hEω
  show ⨆ x : A', ⨆ y : A', Φ (x.1, y.1) (addFunPairing (hC ω) g) = _
  simp only [hω]
  rw [internalDiam_eq_countable hEω hEω.nonneg_apply hδ hAA hAc]
  simp only [iSup_subtype']

end HarmonicBalls
