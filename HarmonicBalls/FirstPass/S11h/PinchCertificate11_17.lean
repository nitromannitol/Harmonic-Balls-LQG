import HarmonicBalls.FirstPass.S11j.CertificateTransfer
import HarmonicBalls.FirstPass.S11h.PairPersistence11_17
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Lemma 11.17: the pair Cameron-Martin transfer through a field-level certificate

Step 17.6 of the corrected paper (lines 3726-3756) transfers the positive probability of the shifted pinch triple back to
the unshifted pair. For a pair `p = (μ, D)` the triple is `pinchPairEvent p = Ẽ₁ ∧ Ẽ₂ ∧ Ẽ₃` (Draft/Section11.lean
lines 95-107). The transfer itself is `cameronMartinFieldCertificateTransfer`, proved from the
frozen `CameronMartinGFFMutualAbsCont`. It needs one common measurable field event `B` that certifies both the pair event of
`(μ ω, D ω)` and that of the Weyl-shifted pair `weylShiftPair γ ξ f (μ ω, D ω)`: this is `PinchFieldCertificate`.

Here: the transfer `pinchPair_transfer_of_certificate` (proved). The certificate is `PinchCertificateStmt`, proved from frozen
inputs by `pinchCertificateStmt_of_frozen` (PinchCertificateProof11_17.lean) through the field-level decoders of the scalar
quantities of the three events.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The conjunction `Ẽ₁ ∧ Ẽ₂ ∧ Ẽ₃` of the three pinch events of a pair `p = (μ, D)` (Lemma 11.17). -/
def pinchPairEvent (U V W T Q' Q : Set ℂ) (δ M : ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) : Prop :=
  pinchFirstEvent p.2 W T Q' Q δ ∧ pinchSecondEvent p.1 p.2 U V δ M ∧ pinchThirdEvent p.2 V W δ

/-- The field-level certificate of Step 17.6 for the shift `f`: one measurable field event `B` (for the σ-algebra of
pairings `distributionMeasurableSpace`) such that, almost surely, the pair event of `(μ ω, D ω)` holds iff the field
`hC ω` lies in `B`, and the pair event of the Weyl-shifted pair holds iff the shifted field `hC ω + f` lies in `B`. -/
def PinchFieldCertificate {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ) (f : ℂ → ℝ)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
    (∀ᵐ ω ∂P, (pinchPairEvent U V W T Q' Q δ M (μ ω, D ω) ↔ hC ω ∈ B)) ∧
    (∀ᵐ ω ∂P, (pinchPairEvent U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω)) ↔ addFunPairing (hC ω) f ∈ B))

/-- Step 17.6 from a field-level certificate: if the Weyl-shifted pinch triple has positive probability, then the pinch
triple of the unshifted pair holds on a measurable event of positive probability. Proved from the frozen
`CameronMartinGFFMutualAbsCont` through `cameronMartinFieldCertificateTransfer`. -/
theorem pinchPair_transfer_of_certificate (hCM : CameronMartinGFFMutualAbsCont.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ ξ : ℝ) (f : ℂ → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f)
    (hcirc0 : Real.circleAverage f 0 1 = 0)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hcert : PinchFieldCertificate P γ ξ f U V W T Q' Q δ M hC μ D)
    (hpos : 0 < P {ω | pinchPairEvent U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω))}) :
    ∃ A ⊆ {ω | pinchPairEvent U V W T Q' Q δ M (μ ω, D ω)}, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨B, hB, hE0, hEf⟩ := hcert
  have key := cameronMartinFieldCertificateTransfer hCM Ω P hC hcirc f hGFF hsm hcs hcirc0
    {ω | pinchPairEvent U V W T Q' Q δ M (μ ω, D ω)}
    {ω | pinchPairEvent U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω))} ⟨B, hB, hE0, hEf⟩
  exact key.2.2.2 hpos

/-- Step 17.6, field-level certificate, proved from frozen inputs by `pinchCertificateStmt_of_frozen`
(PinchCertificateProof11_17.lean). For every buffered pinch geometry, every
`γ ∈ (0, 2)`, `α₀ < Q`, `ξ > 0`, every smooth compactly supported shift `f` vanishing on the unit circle, on `U` and on the
annulus `𝔸_{3,6}(0)`, every whole-plane GFF carrier with its LQG measure and metric, and every `M > 0`, the pair event
admits the field-level certificate `PinchFieldCertificate`.
Written source: corrected paper lines 3726-3756 (Step 17.6). The scalar field versions are the frozen decoders: the internal metric and set distances via
`LQGInternalMetricWeylAeMeasurableFrozen`, masses of `U` via `LQGMassFunctionalMeasurableFrozen`, and the annulus Green
potential `annulusGreenPotentialSup μ 0 3 6` via `exists_annulusGreenField` (S11h/GreenField11_17.lean). The shift `f` only
enters through `f = 0` on `U` and on `𝔸_{3,6}(0)`, where the masses and the annulus potential are unchanged. -/
def PinchCertificateStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < ξ →
  ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  (∀ z ∈ U, f z = 0) → (∀ z ∈ annulus 0 3 6, f z = 0) → ∀ M : ℝ, 0 < M →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    PinchFieldCertificate P γ ξ f U V W T Q' Q δ M hC μ D

/-- A function vanishing on the unit circle has zero unit-circle average (the normalisation used by
`CameronMartinGFFMutualAbsCont`). -/
theorem circleAverage_zero_of_sphere {f : ℂ → ℝ} (hf : ∀ z : ℂ, ‖z‖ = 1 → f z = 0) :
    Real.circleAverage f 0 1 = 0 := by
  rw [Real.circleAverage_def]
  have h0 : ∀ θ : ℝ, f (circleMap 0 1 θ) = 0 := fun θ =>
    hf _ (by simp [norm_circleMap_zero])
  simp [h0]

/-- A shift `φ` supported in `thickening (5δ) W` with `W ⊆ 𝔸_{1,2}(0)` and `δ < 1/1000` vanishes on the annulus
`𝔸_{3,6}(0)`: the thickened set lies in `B_{2+5δ}(0)`. -/
theorem bump_zero_on_annulus {W : Set ℂ} {δ : ℝ} (hW : W ⊆ annulus 0 1 2) (hδ : δ < 1 / 1000) {φ : ℂ → ℝ}
    (hφsupp : ∀ z, z ∉ thickening (5 * δ) W → φ z = 0) : ∀ z ∈ annulus 0 3 6, φ z = 0 := by
  intro z hz
  apply hφsupp
  intro hzW
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hzW
  have hw2 : w ∈ ball (0 : ℂ) 2 := (show w ∈ ball (0 : ℂ) 2 \ closedBall (0 : ℂ) 1 from hW hw).1
  have hz' : z ∈ ball (0 : ℂ) 6 \ closedBall (0 : ℂ) 3 := hz
  have hzd : 3 < dist z 0 := by
    have h := hz'.2
    rw [Metric.mem_closedBall, not_le] at h
    exact h
  have hwd : dist w 0 < 2 := mem_ball.1 hw2
  have htri := dist_triangle z w (0 : ℂ)
  linarith

end HarmonicBalls
