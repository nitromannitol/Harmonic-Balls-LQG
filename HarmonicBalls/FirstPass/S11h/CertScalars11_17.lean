import HarmonicBalls.FirstPass.S11h.PinchCertificate11_17

/-!
# First pass, Lemma 11.17: the scalar form of the pinch certificate (fp-S11h, owner n2)

The pinch triple `pinchPairEvent` is a strict-inequality predicate on ten `ℝ≥0∞`-valued scalars of the pair `(μ, D)`
(`pinchScalars`, `pinchPred`). A field-level certificate `PinchFieldCertificate` follows from one measurable field functional
`Φ` on distributions whose ten coordinates represent the scalars at the field `hC ω` and at the shifted field
`addFunPairing (hC ω) f` almost surely (`pinchFieldCertificate_of_versions`). Constructing such a `Φ` is the remaining work
of `PinchCertificateStmt`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The five strict inequalities of the pinch triple, on the ten scalars of `pinchScalars`. -/
def pinchPred (v : Fin 10 → ℝ≥0∞) : Prop :=
  (v 0 < v 1 ∧ v 2 < v 3) ∧ (v 4 < v 5 ∧ v 6 < v 7) ∧ v 8 < v 9

/-- The ten scalars of a pair `p = (μ, D)` entering the pinch triple, in the order of `pinchPred`: the internal supremum
over `∂B₅` in the corridor `(B_{2δ}(Q ∪ W))ᶜ` and `D(Q', ∂Q)`; `diam^δ(T \ B_{3δ}(W))` and `D(0, ∂B_δ)` (`Ẽ₁`);
`diam^δ(V)` and `D(∂B_δ, ∂B_{2δ})`, then `M · SG_{3,6}(0)` and `μ(U)` (`Ẽ₂`); `diam^δ(B_{3δ}(W) \ V)` and
`D(∂B_{2δ}, ∂B_{3δ})` (`Ẽ₃`). -/
noncomputable def pinchScalars (U V W T Q' Q : Set ℂ) (δ M : ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    Fin 10 → ℝ≥0∞ :=
  ![⨆ y ∈ sphere (0 : ℂ) 5, internalMetric p.2 (thickening (2 * δ) (Q ∪ W))ᶜ 0 y,
    ENNReal.ofReal (setDist p.2 Q' (frontier Q)),
    internalDiam p.2 δ (T \ thickening (3 * δ) W),
    ENNReal.ofReal (setDist p.2 {0} (sphere 0 δ)),
    internalDiam p.2 δ V,
    ENNReal.ofReal (setDist p.2 (sphere 0 δ) (sphere 0 (2 * δ))),
    ENNReal.ofReal M * annulusGreenPotentialSup p.1 0 3 6,
    p.1 U,
    internalDiam p.2 δ (thickening (3 * δ) W \ V),
    ENNReal.ofReal (setDist p.2 (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))]

theorem measurableSet_pinchPred : MeasurableSet {v : Fin 10 → ℝ≥0∞ | pinchPred v} := by
  unfold pinchPred
  simp only [Set.ofPred_and]
  exact (((measurableSet_lt (measurable_pi_apply 0) (measurable_pi_apply 1)).inter
    (measurableSet_lt (measurable_pi_apply 2) (measurable_pi_apply 3))).inter
    (((measurableSet_lt (measurable_pi_apply 4) (measurable_pi_apply 5)).inter
      (measurableSet_lt (measurable_pi_apply 6) (measurable_pi_apply 7))).inter
      (measurableSet_lt (measurable_pi_apply 8) (measurable_pi_apply 9))))

/-- The pinch triple is the predicate `pinchPred` of its ten scalars. -/
theorem pinchPairEvent_iff_pred (U V W T Q' Q : Set ℂ) (δ M : ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    pinchPairEvent U V W T Q' Q δ M p ↔ pinchPred (pinchScalars U V W T Q' Q δ M p) := Iff.rfl

/-- A certificate from scalar field versions: if a measurable predicate `Pred` decides the events `E0`, `Ef` through
the scalars `s ω`, `s' ω`, and a measurable field functional `Φ` represents these scalars at `hC ω` and at
`addFunPairing (hC ω) f` almost surely, then `B = Φ⁻¹(Pred)` is a field certificate for both events. -/
theorem certificate_of_scalar_versions {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (f : ℂ → ℝ) (Pred : (Fin N → ℝ≥0∞) → Prop) (hPred : MeasurableSet {v | Pred v})
    (E0 Ef : Ω → Prop) (s s' : Ω → Fin N → ℝ≥0∞) (Φ : ((ℂ → ℝ) → ℝ) → Fin N → ℝ≥0∞)
    (hΦ : Measurable[distributionMeasurableSpace] Φ)
    (hE0 : ∀ ω, E0 ω ↔ Pred (s ω)) (hEf : ∀ ω, Ef ω ↔ Pred (s' ω))
    (h0 : ∀ᵐ ω ∂P, Φ (hC ω) = s ω) (hf : ∀ᵐ ω ∂P, Φ (addFunPairing (hC ω) f) = s' ω) :
    ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
      (∀ᵐ ω ∂P, E0 ω ↔ hC ω ∈ B) ∧ (∀ᵐ ω ∂P, Ef ω ↔ addFunPairing (hC ω) f ∈ B) := by
  refine ⟨Φ ⁻¹' {v | Pred v}, hΦ hPred, ?_, ?_⟩
  · filter_upwards [h0] with ω hω
    rw [hE0 ω, Set.mem_preimage, Set.mem_ofPred_eq, hω]
  · filter_upwards [hf] with ω hω
    rw [hEf ω, Set.mem_preimage, Set.mem_ofPred_eq, hω]

/-- A pinch field certificate from one measurable field functional `Φ` with the ten scalars of the pair and of the
Weyl-shifted pair as almost sure values at `hC ω` and at `addFunPairing (hC ω) f`. -/
theorem pinchFieldCertificate_of_versions {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ) (f : ℂ → ℝ)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Φ : ((ℂ → ℝ) → ℝ) → Fin 10 → ℝ≥0∞) (hΦ : Measurable[distributionMeasurableSpace] Φ)
    (h0 : ∀ᵐ ω ∂P, Φ (hC ω) = pinchScalars U V W T Q' Q δ M (μ ω, D ω))
    (hf : ∀ᵐ ω ∂P,
      Φ (addFunPairing (hC ω) f) = pinchScalars U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω))) :
    PinchFieldCertificate P γ ξ f U V W T Q' Q δ M hC μ D :=
  certificate_of_scalar_versions P hC f pinchPred measurableSet_pinchPred
    (fun ω => pinchPairEvent U V W T Q' Q δ M (μ ω, D ω))
    (fun ω => pinchPairEvent U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω)))
    (fun ω => pinchScalars U V W T Q' Q δ M (μ ω, D ω))
    (fun ω => pinchScalars U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω)))
    Φ hΦ (fun ω => pinchPairEvent_iff_pred U V W T Q' Q δ M (μ ω, D ω)) (fun ω => pinchPairEvent_iff_pred U V W T Q' Q δ M (weylShiftPair γ ξ f (μ ω, D ω))) h0 hf

end HarmonicBalls
