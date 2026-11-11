import HarmonicBalls.Proofs.Sec11.PinchNormalizedFrequency

/-! # Unit-scale pinch probability and normalized frequency

The Section 8 ergodic theorem used through the normalized-frequency result is
from Leonardo Bonanno's LatticeProb formalization. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- Positive unit-scale probability and stationary normalized local data give
positive block frequency for the internal-bound pinch event. -/
theorem IsWholePlaneGFF.ae_positive_internal_pinch_frequency_of_normalized_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y))
    (hstat : IdentDistrib
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P)
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M 1 0}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let E₀ : Set Ω := {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M 1 0}
  let E₁ : Set Ω := {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
    ((2 : ℝ)⁻¹ ^ 1) 0}
  have hdist := hstat.comp (measurable_pi_apply 0)
  have heq : P E₀ = P E₁ := by
    have h := hdist.measure_mem_eq (measurableSet_singleton (1 : ℝ))
    have hevent (A : Ω → Prop) :
        (fun ω => if A ω then (1 : ℝ) else 0) ⁻¹' {1} = {ω | A ω} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_ofPred_eq]
      split <;> simp_all
    simpa [Function.comp_def, hevent, E₀, E₁] using h
  have hp : 0 < P E₁ := by rw [← heq]; exact hpos
  have hpReal : 0 < (P E₁).toReal := ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P E₁)
  let δ : ℝ := min 1 (P E₁).toReal / 2
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ < 1 := by dsimp [δ]; have := min_le_left (1 : ℝ) (P E₁).toReal; linarith
  have hδprob : δ < (P E₁).toReal := by
    dsimp [δ]; have := min_le_right (1 : ℝ) (P E₁).toReal; linarith
  refine ⟨δ, ⟨hδpos, hδone⟩, ?_⟩
  exact hGFF.ae_internal_pinch_frequency_of_normalized_metric P hμ hfull hD hconfig M
    hmetric hstat δ hδprob


end HarmonicBalls
