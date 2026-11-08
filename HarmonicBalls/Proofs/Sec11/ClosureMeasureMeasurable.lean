import HarmonicBalls.Proofs.Sec11.Closure.PinchEventTypeZero
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Lemma 11.12 at zero log-charge with the measurability of the LQG measure from the GFF (Section 11, draft lines 376–446)

`Closure/PinchEventTypeZero.lean` reduces the body of `PinchEventPositiveProbabilityStmt`
(`HarmonicBalls/Draft/Section11.lean:246`) at `α₀ = 0`, for probability spaces `Ω : Type`, to the raw canonical
positivity `RawCanonicalPositiveStmt`, with the measurability of the measure-valued field as the named premise `haem`.
The universal binder of `haem` quantifies over all `Ω`, `P`, `hcirc` and `μ` and does not contain the whole-plane GFF
hypothesis `IsWholePlaneGFF P hC hcirc`. So the GFF hypothesis of the actual configuration cannot be used to discharge `haem`.

This module removes `haem`. The measurability is supplied by the proved `IsWholePlaneGFF.aemeasurable_lqgMeasure`
(`Proofs/Sec5/OpenMeasureLaw.lean:130`), which takes the GFF hypothesis and the LQG measure property, has no locality
premise, and is stated for arbitrary `α₀` and universe. The proof is that of `pinchEventPositive_typeZero_of_raw` with
this single substitution. The metric bridge (`Closure/MetricBridgeZero.lean`, `Closure/MetricMeasurableZero.lean`), the
measurable positive subset `exists_measurable_pos_subset_pinch` (`Proofs/Sec11/PinchInnerPositivity.lean:38`) and the
removal of a null set are reused unchanged.

The only premise left is the raw canonical positivity `RawCanonicalPositiveStmt`, for the given configuration. This is
conditional raw positivity, not a closure of Lemma 11.12. The fixed configuration of `Closure/FixedGeometry.lean` is
exported as an existential witness, as in `exists_pinchEvent_typeZero_fixed_of_raw`.

Credit: the import closure of this module contains code by Leonardo Bonanno. It reaches the external LatticeProb module
`LatticeProb.Prob.Birkhoff` (his LatticeProb formalization of the ergodic theorem, as credited in
`Steps/Sec11/CountableCoordinateObservables.lean`), and `Proofs/Sec11/WholePlaneMetricLocality.lean`, which states that its
Section 8 inputs use his LatticeProb code, through `Closure/MetricBridgeZero.lean`. This module uses no LatticeProb
declaration directly and adds none.
-/

namespace HarmonicBalls

open MeasureTheory Filter

/-- The Type-zero body of Lemma 11.12 at `α₀ = 0` for `Ω : Type`, from the raw canonical positivity of the given
pinch-point configuration alone. The measurability of the measure-valued field is supplied by
`IsWholePlaneGFF.aemeasurable_lqgMeasure`, so no measurability premise `haem` remains. Credit: the upstream code
of Leonardo Bonanno (LatticeProb) is in the import closure, see the module documentation. -/
theorem pinchEventPositive_typeZero_of_raw_gff {U T Q' Q : Set ℂ}
    (hconfig : IsPinchPointConfiguration U T Q' Q) (hraw : RawCanonicalPositiveStmt U T Q' Q) :
    ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
      ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet A ∧ 0 < P A := by
  intro γ ξ hγ hγ' Ω _ P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨𝔇, h𝔇, hbridge⟩ := ae_metric_eq_canonical_of_isLQGMetricOfField_zero hgff hD
  have hpos := hraw γ ξ hγ hγ' Ω P hC hcirc μ 𝔇 hgff hμ h𝔇 M hM
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero hgff hD, hbridge]
      with ω h1 h2
    rw [← h2]
    exact h1
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    Eventually.mono hμ (fun ω hω => hω.isLocallyFiniteMeasure)
  obtain ⟨E, hsub, hE, hEpos⟩ :=
    exists_measurable_pos_subset_pinch P hconfig M 0 (by norm_num : (0 : ℝ) < 1)
      (D := fun ω => 𝔇 (hC ω)) (fun x y => measurable_canonical_metric hgff 𝔇 h𝔇 x y)
      hmetric (hgff.aemeasurable_lqgMeasure hμ) hloc hpos
  set S : Set Ω := {ω | ¬ (D ω = 𝔇 (hC ω))} with hS
  have hS0 : P (toMeasurable P S) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hbridge
  refine ⟨E \ toMeasurable P S, ?_, ?_, ?_⟩
  · intro ω hω
    have hωS : ω ∉ toMeasurable P S := hω.2
    have heq : D ω = 𝔇 (hC ω) := by
      by_contra hne
      exact hωS (subset_toMeasurable P S hne)
    have hpe : pinchPointEvent (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0 := (hsub hω.1).1
    show pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0
    rw [heq]
    exact hpe
  · exact hE.diff (measurableSet_toMeasurable P S)
  · rw [measure_sdiff_null hS0]
    exact hEpos

/-- The fixed pinch-point configuration (`Closure/FixedGeometry.lean`) with the Type-zero body of Lemma 11.12, from the
raw canonical positivity of the fixed configuration alone: the existential witness `∃ U T Q' Q` of
`PinchEventPositiveProbabilityStmt`. The measurability is supplied by the GFF, as in
`pinchEventPositive_typeZero_of_raw_gff`. Conditional on the raw positivity; not a closure of Lemma 11.12. -/
theorem exists_pinchEvent_typeZero_fixed_of_raw_gff
    (hraw : RawCanonicalPositiveStmt fixedU fixedT fixedQ' fixedQ) :
    ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
      ∀ (γ ξ : ℝ), 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        IsLQGMetricOfField P γ ξ 0 hC D → ∀ M : ℝ, 0 < M →
        ∃ A ⊆ {ω | pinchPointEvent (μ ω) (D ω) fixedU fixedT fixedQ' fixedQ M 1 0},
          MeasurableSet A ∧ 0 < P A := by
  refine ⟨fixedU, fixedT, fixedQ', fixedQ, isPinchPointConfiguration_fixed, ?_⟩
  exact pinchEventPositive_typeZero_of_raw_gff isPinchPointConfiguration_fixed hraw

#print axioms pinchEventPositive_typeZero_of_raw_gff
#print axioms exists_pinchEvent_typeZero_fixed_of_raw_gff

end HarmonicBalls
