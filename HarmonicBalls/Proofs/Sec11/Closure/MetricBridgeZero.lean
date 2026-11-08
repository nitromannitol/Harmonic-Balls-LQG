import HarmonicBalls.Proofs.Sec11.WholePlaneMetricLocality

/-!
# Metric bridge at zero log-charge (Section 11, draft lines 46–269)

For a whole-plane GFF `hC` on a probability space `Ω : Type` and an arbitrary metric map `D` satisfying
`IsLQGMetricOfField P γ ξ 0 hC D` (the γ-LQG metric of the field with `α₀ = 0`, `Defs/LQGMetric.lean`), the
metric agrees almost surely with the canonical functional `𝔇 (hC ω)`, and is a Euclidean length metric almost
surely. This is the bridge from an arbitrary metric map to the canonical one used by the conditional chain of
Lemma 11.12 (`PinchEventPositiveProbabilityStmt`, `HarmonicBalls/Draft/Section11.lean:246`).

The agreement is the existing `IsWholePlaneGFF.ae_zeroCharge_metric_eq_base`
(`Proofs/Sec11/WholePlaneMetricLocality.lean:45`), applied to the almost-sure Weyl identity that
`IsLQGMetricOfField` supplies at `α₀ = 0`. The universe is `Ω : Type`, the universe of `IsLQGMetric`'s axioms
(open point R7 of the status note); the universe-general statement is not claimed here.
-/

namespace HarmonicBalls

open MeasureTheory

/-- The zero-charge Weyl identity of `IsLQGMetricOfField` at `α₀ = 0`, with `-0 · log` simplified away. -/
lemma isLQGMetricOfField_zero_weyl {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧ ∀ᵐ ω ∂P, ∀ u v,
      0 ≤ D ω u v ∧ ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ 0 u v := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hf : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = 0 := by
    funext x
    simp
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hrepr] with ω hω u v
  simpa only [hf] using hω u v

/-- Metric bridge at `α₀ = 0`: an arbitrary metric map `D` with `IsLQGMetricOfField P γ ξ 0 hC D` agrees almost
surely with the canonical LQG metric `𝔇 (hC ω)` of the GFF (`𝔇` as in `IsLQGMetric`). -/
theorem ae_metric_eq_canonical_of_isLQGMetricOfField_zero {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧ ∀ᵐ ω ∂P, D ω = 𝔇 (hC ω) := by
  obtain ⟨𝔇, h𝔇, hD'⟩ := isLQGMetricOfField_zero_weyl hD
  exact ⟨𝔇, h𝔇, h.ae_zeroCharge_metric_eq_base 𝔇 h𝔇 hD'⟩

/-- `addFunPairing F` with the zero function is the identity on pairing functionals. -/
lemma addFunPairing_zero_fun (F : (ℂ → ℝ) → ℝ) :
    addFunPairing F (fun _ => 0) = F := by
  funext φ
  simp [addFunPairing]

/-- Metric bridge at `α₀ = 0`, length-metric part: under the same hypotheses, `D ω` is almost surely a
Euclidean length metric (`IsEuclideanLengthMetric`), the axiom I of `SatisfiesLQGMetricAxioms` applied to the
zero continuous perturbation of the GFF. -/
theorem ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hbridge⟩ := ae_metric_eq_canonical_of_isLQGMetricOfField_zero h hD
  have hbase := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hbase' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    simpa only [addFunPairing_zero_fun] using hbase
  filter_upwards [hbridge, hbase'] with ω hω1 hω2
  rw [hω1]
  exact hω2

#print axioms ae_metric_eq_canonical_of_isLQGMetricOfField_zero
#print axioms ae_isEuclideanLengthMetric_of_isLQGMetricOfField_zero

end HarmonicBalls
