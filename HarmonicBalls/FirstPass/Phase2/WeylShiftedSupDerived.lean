import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.FirstPass.Frozen.S11j

/-! # Weyl-shifted internal metric: field-shift identity and a.e. measurability at fixed endpoints (phase 2, worker z4)

Staged work towards `WeylShiftedSupMeasurableFrozen` (FirstPass/Frozen/S11c.lean:217). Only frozen inputs whose status
row in docs/campaign/PHASE2-INPUT-STATUS.md is TRUE are used, each as an explicit hypothesis:

* `LQGMetricFieldAxiomsUnivFrozen` (row 58; clause I finiteness and Euclidean length, clause III Weyl scaling);
* `WeylScalingCompositionFrozen` (row 34);
* `LQGInternalMetricWeylAeMeasurableFrozen` (row 36);
* `InternalMetricClosedEqIInfThickeningFrozen` (row 47);
* `WeylScaledEuclideanFrozen` (row 48).

Proved here, with no hypothesis beyond these:

* `weylShiftPair_snd_ae_eq_field_shift`: almost surely the Weyl-shifted metric `(weylShiftPair γ ξ f (μ, D)).2` equals the
  metric of the shifted field `h^ℂ + f` at insertion `α₀`.
* `measurable_addFunPairing_distribution`: `h ↦ h + f` is measurable for `distributionMeasurableSpace`.
* `weylShiftInternalMetric_aemeasurable_closed`: for a closed `S` and fixed `u v ∈ S`, `ω ↦ internalMetric (weylShift) S u v`
  is a.e. measurable.

NOT proved here: `WeylShiftedSupMeasurableFrozen` itself. Its supremum is over all `u v ∈ S` (uncountable). The reduction
is `aemeasurable_iSup_mem_of_lowerSemicontinuousOn` (HarmonicBalls/LPStage/WeylSupMeasurable.lean) applied with
`D = D₀ ×ˢ D₀` for a countable dense `D₀ ⊆ S`. It needs, for almost every `ω` and every closed dyadic square `S`,
`LowerSemicontinuousOn (fun p : ℂ × ℂ => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S p.1 p.2) (S ×ˢ S)`.
No input whose status row is TRUE gives this (BLOCKED; see reports/z4.md). -/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

universe u

/-- Almost surely, the Weyl-shifted metric `(weylShiftPair γ ξ f (μ, D)).2` of an LQG metric `D` (the unfolded body of
`IsLQGMetricOfField`, for the metric `𝔇` of `h^ℂ`) equals the metric `weylScaling (𝔇 (h^ℂ + f)) ξ (-α₀ log|·|)` of the shifted
field. Clause III of `LQGMetricFieldAxioms` (TRUE, row 58) and `WeylScalingCompositionFrozen` (TRUE, row 34) are used. -/
theorem weylShiftPair_snd_ae_eq_field_shift {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hW : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∀ᵐ ω ∂P, (weylShiftPair γ ξ f (μ ω, D ω)).2 =
      fun u v => (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal := by
  have hIII := ((hAx Ω P γ ξ α₀ hC hcirc) hW hγ0 hγ2 hα 𝔇 h𝔇).2.2.1
  have hWSCf := hWSC γ ξ α₀ Ω P hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇 f hf
  filter_upwards [hD, hIII, hWSCf] with ω hDω hIIIω hWω
  funext u v
  have hDeq : D ω = fun a b => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
    funext a b
    obtain ⟨h0, h1⟩ := hDω a b
    rw [← h1, ENNReal.toReal_ofReal h0]
  show (weylScaling (D ω) ξ f u v).toReal = _
  rw [hDeq, ← hIIIω f hf u v, hWω u v]

/-- For a whole-plane GFF, the shifted distribution `h ↦ h + f` (`addFunPairing`) is measurable for the
distribution σ-algebra `distributionMeasurableSpace`: its value at each test function `φ` is `h(φ) + ∫ f φ`. -/
theorem measurable_addFunPairing_distribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) (f : ℂ → ℝ) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace fun ω => addFunPairing (hC ω) f := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 ((hW.measurable_pairing φ hφ).add_const _)

/-- For a closed set `S` and fixed `u v ∈ S`, the internal metric of the Weyl-shifted metric is almost surely measurable.
Route: the closed-set identity `InternalMetricClosedEqIInfThickeningFrozen` (row 47) writes it as `⨅ n, ⨆ k` of the
internal metrics on the open thickenings of `S ∩ closedBall 0 (n+1)`; on each open set the internal metric of the
Weyl-shifted metric equals a.s. `Φ (h^ℂ + f)` for a measurable `Φ` (`LQGInternalMetricWeylAeMeasurableFrozen`, row 36). -/
theorem weylShiftInternalMetric_aemeasurable_closed {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ ξ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hW : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (hInt : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hClos : InternalMetricClosedEqIInfThickeningFrozen)
    (hEuc : WeylScaledEuclideanFrozen)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (f : ℂ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (S : Set ℂ) (hS : IsClosed S) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S) :
    AEMeasurable (fun ω => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S u v) P := by
  have hK := weylShiftPair_snd_ae_eq_field_shift P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα hAx hWSC 𝔇 h𝔇 D μ hD f hf
  have hEucD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [(hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇).1, hD] with ω hI hDω
    have hDeq : D ω = fun a b => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
      funext a b
      obtain ⟨h0, h1⟩ := hDω a b
      rw [← h1, ENNReal.toReal_ofReal h0]
    rw [hDeq]
    exact hI.2
  have hClosedω : ∀ᵐ ω ∂P, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S u v =
      ⨅ n : ℕ, ⨆ k : ℕ, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2
        (Metric.thickening (((k : ℝ) + 1)⁻¹) (S ∩ Metric.closedBall 0 ((n : ℝ) + 1))) u v := by
    filter_upwards [hEucD] with ω hE
    exact hClos _ S hS (hEuc (D ω) ξ f hE hf hfc) hu hv
  have hex : ∀ n k : ℕ, ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ g : ℂ → ℝ, Continuous g → ∀ᵐ ω ∂P,
        Φ (addFunPairing (hC ω) g) = internalMetric
          (fun a b => (weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -α₀ * Real.log ‖z‖) a b).toReal)
          (Metric.thickening (((k : ℝ) + 1)⁻¹) (S ∩ Metric.closedBall 0 ((n : ℝ) + 1))) u v := fun n k =>
    hInt γ ξ α₀ Ω P hC hcirc 𝔇 hW hγ0 hγ2 hα h𝔇 _ Metric.isOpen_thickening u v
  choose Φ hΦm hΦeq using hex
  have hΦae : ∀ᵐ ω ∂P, ∀ n k : ℕ, Φ n k (addFunPairing (hC ω) f) = internalMetric
      (fun a b => (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) a b).toReal)
      (Metric.thickening (((k : ℝ) + 1)⁻¹) (S ∩ Metric.closedBall 0 ((n : ℝ) + 1))) u v :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hΦeq n k f hf
  have hmeasFP := measurable_addFunPairing_distribution hW f
  have hmeas : AEMeasurable (fun ω => ⨅ n : ℕ, ⨆ k : ℕ, Φ n k (addFunPairing (hC ω) f)) P :=
    AEMeasurable.iInf fun n => AEMeasurable.iSup fun k =>
      ((hΦm n k).comp hmeasFP).aemeasurable
  refine hmeas.congr ?_
  filter_upwards [hK, hΦae, hClosedω] with ω hKω hΦω hCω
  rw [hCω, hKω]
  simp only [hΦω]

end HarmonicBalls
