import HarmonicBalls.FirstPass.S11h.CoordDistDiam11_17
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.Proposed.LQG

/-!
# First pass, Lemma 11.17: the metric of the Weyl-shifted pair equals the field metric of the shifted field
(fp-S11h, owner n2)

For a pair `(μ ω, D ω)` and a continuous shift `f`, the Weyl-shifted pair of `weylShiftPair` carries the metric
`u v ↦ (weylScaling (D ω) ξ f u v).toReal`. The field decoders of `CoordDistDiam11_17.lean` are stated for
`fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)`. This file identifies the two almost surely: the Weyl identity III of the
metric axioms (`LQGMetricFieldAxioms`, Fact 2.2 III, Proposed/LQG.lean) for the unshifted field, and the composition
identity `WeylScalingCompositionFrozen` (Frozen/S11d.lean) for the shifted field.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The metric of the Weyl-shifted pair `weylShiftPair γ ξ f (μ ω, D ω)` is the field metric of the shifted field,
almost surely: `(weylScaling (D ω) ξ f).toReal = fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)`. -/
theorem ae_weylScaling_toReal_eq_fieldMetric_shift
    (hComp : WeylScalingCompositionFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hAx : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (f : ℂ → ℝ) (hf : Continuous f) :
    ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧
      ∀ᵐ ω ∂P, (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
        fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨-, -, hIII, -⟩ := hAx hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hcomp := hComp γ ξ α₀ Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇 f hf
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hIII, hDae, hcomp] with ω hω hDω hc
  have hDeq : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) = D ω := by
    funext u v
    rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
  funext u v
  unfold fieldMetric
  rw [hc u v, hω f hf u v, ← hDeq]

/-! ## NEW steps for the coordinate assembly of Lemma 11.17 (pending operator decision; NOT frozen, NOT proved)

Both are used only as explicit hypotheses of the reduction `pinchCertificateStmt_of_newSteps` (to be written): they are
not inputs of any Draft statement. -/

/-- NEW STEP N1 (coordinate 0 of `pinchScalars`: the closed-corridor internal supremum, field level). For a closed
corridor `C ∋ 0` containing the sphere `∂B_5(0)`, the supremum over `∂B_5(0)` of the internal metric of `C` (the
closed set, paper line 429 defines `internalMetric` for open sets only: printed inconsistency Q2) is the value of a
measurable field functional `Φ` at the shifted field, almost surely. Blocked on K1
(`internalMetric D C x y = ⨅ n, ⨆ k, internalMetric D (thickening ((k+1)⁻¹) (C ∩ closedBall 0 (n+1))) x y` for closed `C`,
`x y ∈ C`), which has only a sketch (notes/fp-gaps/CHATGPT-cm-field-certificate.md §3.3). -/
def CorridorInternalSupFieldStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetric γ ξ 𝔇 →
    ∀ C : Set ℂ, IsClosed C → (0 : ℂ) ∈ C → sphere (0 : ℂ) 5 ⊆ C →
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g →
        (∀ᵐ ω ∂P, IsEuclideanLengthMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g))) →
        ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) g) =
          ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (fieldMetric 𝔇 ξ α₀ (addFunPairing (hC ω) g)) C 0 y

/-- NEW STEP N2 (Euclidean property of a continuous Weyl scaling). For a Euclidean length metric `D` and a continuous
compactly supported shift `f`, the Weyl-scaled metric `(weylScaling D ξ f).toReal` is again a Euclidean length metric.
Truth: the weights `exp(ξ f)` are bounded above and below, so the weighted metric is bi-Lipschitz to `D`, and the length
property follows from the triangle inequality. No written argument in the repository: the Steps modules take this
property as a hypothesis (`Steps/Sec11/WeylInversePath.lean:20`, `Steps/Sec11/WeylInverse.lean:17`). -/
def WeylScaledEuclideanStmt : Prop :=
  ∀ (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ), IsEuclideanLengthMetric D → Continuous f → HasCompactSupport f →
    IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal)

end HarmonicBalls
