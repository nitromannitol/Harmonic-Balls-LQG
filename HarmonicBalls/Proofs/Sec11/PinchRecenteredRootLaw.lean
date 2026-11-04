import HarmonicBalls.Proofs.Sec11.PinchDominatingLaw

/-! # Rooted comparison after recentering

A common fixed-root law supplies one density rate at every root. The
realization of recentering and its absolute-continuity comparison are
explicit hypotheses.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A density estimate at the origin passes to a fixed root when the
recentered comparison law is absolutely continuous with respect to the
origin law. -/
theorem ae_internal_pinch_block_density_of_recentered_comparison
    {Ω : Type*} [MeasurableSpace Ω] (R Q : Measure Ω)
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (U T Q' Qset : Set ℂ) (M q : ℝ) (r : ℕ → ℝ) (z : ℂ)
    (recenter : Ω → Ω) (hrec : AEMeasurable recenter R)
    (hac : R.map recenter ≪ Q)
    (heq : ∀ᵐ ω ∂(R), μ (recenter ω) = (μ ω).map (fun y : ℂ => y - z) ∧
      ∀ x y, D (recenter ω) x y = D ω (x + z) (y + z))
    (hfixed : ∀ᵐ ω ∂(Q), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) 0}.ncard : ℝ)) :
    ∀ᵐ ω ∂(R), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) z}.ncard : ℝ) := by
  have h := ae_of_ae_map hrec (hac.ae_le hfixed)
  filter_upwards [h, heq] with ω hω ⟨hμ, hD⟩
  have hpoint (k : ℕ) :
      pinchPointEventWithInternalBounds (μ (recenter ω)) (D (recenter ω))
          U T Q' Qset M (r k) 0 ↔
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) z := by
    rw [hμ, show D (recenter ω) = fun x y => D ω (x + z) (y + z) from funext fun x => funext (hD x)]
    exact pinchPointEventWithInternalBounds_translate (μ ω) (D ω) U T Q' Qset M (r k) z
  have hsets (N : ℕ) :
      {k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ (recenter ω)) (D (recenter ω))
          U T Q' Qset M (r k) 0} =
      {k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M (r k) z} := by
    ext k
    simp only [mem_ofPred_eq, hpoint]
  filter_upwards [hω] with N hN
  simpa only [hsets] using hN

/-- A single origin law supplies the same block-density rate for almost every
root, conditional on the rooted and recentered comparison laws. -/
theorem ae_ae_pinch_block_density_of_recentered_rooted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ν : ℕ → Measure Ω) (hμν : ∀ n, AEMeasurable μ (ν n))
    (hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω))
    (hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (D ω))
    {U T Q' Qset : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Qset)
    (M q : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ ν n)
    (recenter : ℂ → Ω → Ω) (hrec : ∀ n, ∀ᵐ z ∂ρ n, AEMeasurable (recenter z) (R n z))
    (Q : Measure Ω) (hcomp : ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (recenter z) ≪ Q)
    (heq : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      μ (recenter z ω) = (μ ω).map (fun y : ℂ => y - z) ∧
        ∀ x y, D (recenter z ω) x y = D ω (x + z) (y + z))
    (hfixed : ∀ᵐ ω ∂(Q), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  apply ae_ae_pinch_block_density_of_countably_dominated_rooted_law
    P hμ hloc hD hmetric ν hμν hlocν hmetricν hconfig M q w hw hpos hfin
    ρ shift hshift R hrooted hac hdom
  intro n
  filter_upwards [hrec n, hcomp n, heq n] with z hr hc he
  exact ae_internal_pinch_block_density_of_recentered_comparison (R n z) Q
    U T Q' Qset M q (fun k => (2 : ℝ)⁻¹ ^ k) z (recenter z) hr hc he hfixed

#print axioms ae_ae_pinch_block_density_of_recentered_rooted_law

#print axioms ae_internal_pinch_block_density_of_recentered_comparison

end HarmonicBalls
