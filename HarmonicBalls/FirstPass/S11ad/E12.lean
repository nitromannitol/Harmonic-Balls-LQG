import HarmonicBalls.FirstPass.S11ab
import HarmonicBalls.FirstPass.S11y
import HarmonicBalls.FirstPass.S11ad.E1Shift
import HarmonicBalls.FirstPass.S11ad.ExteriorA
import HarmonicBalls.FirstPass.S11ad.ExteriorE1

/-!
# Positivity of `E₁ ∩ E₂` on a set measurable outside `closure W` (note §6.2-6.3)

* Step 1: the shifted first event has positive probability on the good box (`exists_E1_shift_pos`).
* Step 2: Cameron-Martin transfer of `E₁` to the base field (`metric_event_transfer_of_rule`). Its rule input
  `hE1rule` is `MetricEventCertificateStmt` for `E₁` (discharged for `E₁` in task fp-S11ae, taken as a hypothesis
  here); its shift clause `hE1shift` is a named hypothesis pending operator decision R4.
* Step 3: the outside-`W` version `G` of `E₁` (`pinchFirstEventLocal_exterior_version`) has positive probability.
* Step 4: `S11y.pinchLocal_E2_positive` with `F := G` gives a measurable `A ⊆ G` of positive probability on which
  `E₁` and `E₂` hold.

Names follow Armstrong-Kuusi-Mourrat (internal metric, Weyl scaling) and Duplantier-Sheffield (LQG metric).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls
namespace S11ad

/-- The bump family of the §6.2 shift: the weights `ξ⁻¹ (log b φ_Q ...)` of `exists_E1_shift_pos`, i.e. the
functions `shiftWeight ξ b bQ φQ φ0` for `1 ≤ b`, `1 ≤ bQ` and bumps `φQ`, `φ0` with the bump conditions of
`exists_E1_shift_pos`. -/
def E1ShiftSet (Q : Set ℂ) (δ ξ : ℝ) :
    Set (ℂ → ℝ) :=
  {f | ∃ b bQ : ℝ, 1 ≤ b ∧ 1 ≤ bQ ∧ ∃ φQ φ0 : ℂ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φQ ∧ HasCompactSupport φQ ∧
    (∀ z ∈ closure Q, φQ z = 1) ∧ (∀ z, z ∉ thickening δ Q → φQ z = 0) ∧ (∀ z, φQ z ∈ Icc (0 : ℝ) 1) ∧
    ContDiff ℝ (⊤ : ℕ∞) φ0 ∧ HasCompactSupport φ0 ∧
    (∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) ∧ (∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) ∧
    (∀ z, φ0 z ∈ Icc (0 : ℝ) 1) ∧ f = HarmonicBalls.shiftWeight ξ b bQ φQ φ0}

/-- Positivity of `E₁ ∩ E₂` on a measurable set (note §6.2-6.3). The output `A` is measurable for the full
sigma-algebra and `E₁`, `E₂` hold on `A`. Named hypotheses: `hE1rule` (rule measurability for `E₁`, task
fp-S11ae) and `hE1shift` (the shift clause of `metric_event_transfer_of_rule`, for every admissible bump weight;
pending operator decision R4). -/
theorem pinchLocal_E12_pos (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hS : BundleParts.PinchSecondAnnulusStep.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (γ α₀ ξ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D) (M : ℝ)
    (hE1rule : MetricEventCertificateStmt.{u} γ ξ (fun E => pinchFirstEventLocal E W T Q' Q δ))
    (hE1shift : ∀ f ∈ E1ShiftSet Q δ ξ, ∀ B : Set ((ℂ → ℝ) → ℝ),
      MeasurableSet[distributionMeasurableSpace] B →
      (∀ᵐ ω ∂P, hC ω ∈ B ↔ pinchFirstEventLocal (D ω) W T Q' Q δ) →
      ∀ᵐ ω ∂P, pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ →
        addFunPairing (hC ω) f ∈ B) :
    ∃ A : Set Ω, MeasurableSet A ∧ 0 < P A ∧
      ∀ ω ∈ A, pinchFirstEventLocal (D ω) W T Q' Q δ ∧ pinchSecondEventLocal (μ ω) (D ω) U V δ M := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    (metric_locality_of_frozen hAx γ ξ α₀ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDm).1
  -- Step 1: shifted first event on the good box
  obtain ⟨b, bQ, hb, hbQ, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I,
    hs1, hs2, hs4, hpos⟩ :=
    exists_E1_shift_pos hG hΩ D hmetric hξ
  -- Step 2: Cameron-Martin transfer of `E₁` to the base field
  obtain ⟨A1, hA1sub, hA1m, hA1p⟩ :=
    metric_event_transfer_of_rule hCM hE1rule P hC hcirc hGFF α₀ hα D hDm
      (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) hs1 hs2 hs4
      (fun ω x y => (weylScaling (D ω) ξ (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) x y).toReal)
      (hE1shift (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) ⟨b, bQ, hb, hbQ, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I, rfl⟩)
      hpos
  -- Step 3: the outside-`W` version `G` of `E₁`
  obtain ⟨G, hGm, hGae⟩ :=
    pinchFirstEventLocal_exterior_version hAx U V W T Q' Q δ hG γ ξ α₀ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDm hΩ
  have hGpos : 0 < P G := by
    refine lt_of_lt_of_le hA1p (measure_mono_ae ?_)
    filter_upwards [hGae] with ω hω hωA
    exact hω.2 (hA1sub hωA)
  have hFE1 : ∀ᵐ ω ∂P, ω ∈ G → pinchFirstEventLocal (D ω) W T Q' Q δ := by
    filter_upwards [hGae] with ω hω hωG
    exact hω.1 hωG
  -- Step 4: local second event on `G`
  obtain ⟨A2, hA2m, hA2sub, hA2p, hA2E⟩ :=
    S11y.pinchLocal_E2_positive hAx hD hM hDiam hMk hS U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D
      hGFF hμ hDm G hGm hGpos hFE1 M
  exact ⟨A2, hA2m, hA2p, hA2E⟩

end S11ad
end HarmonicBalls
