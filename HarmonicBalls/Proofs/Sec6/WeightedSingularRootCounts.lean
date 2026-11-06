import HarmonicBalls.Proofs.Sec6.LocalizedWeightedRootKernel

/-! # Singular annulus counts for weighted local roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

open Classical in
/-- Sampling from a weighted singular LQG restriction to a middle annulus
supplies the root localization in the finite count estimate. Collar failure
probabilities and the zero-strength root count remain explicit. -/
theorem exists_weighted_singularRoot_goodAnnulus_count_probability_le
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (ρ : ℝ) (x₀ : ℂ) (hρ : 0 < ρ)
    (v : ℂ → ℝ≥0∞) (hv : Measurable v)
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ → ℝ), (∀ i, 0 < r i) →
      ∀ (s : Finset ℕ) (a a' amid b b' : ℝ) (d : ℝ≥0∞) (m k : ℕ),
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) *
        (ENNReal.ofReal (((401 : ℝ) ^ |-(γ * α)|) ^ 2) * d) ≤ ENNReal.ofReal amid →
      ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2*ρ)) →
      (∀ i ∈ s, 5*r i + η*r i < ρ/4) →
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
        (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) w
          (a' / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b').card < m} ≤
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p |
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k} +
      ∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  classical
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
  have hk := weightedRestrictionKernel_middle_annulus P μ (h.aemeasurable_lqgMeasure hμ) x₀ ρ v hv
  obtain ⟨δ, hδ, ht⟩ := exists_localized_singularRoot_goodAnnulus_count_probability_le
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hk.1 hη hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr s a a' amid b b' d m k hbudget hmid hslack hsep hsmall
  exact ht r hr s ρ x₀ hρ a a' amid b b' d m k hbudget hmid hslack hsep hsmall hk.2

end HarmonicBalls.Section6
