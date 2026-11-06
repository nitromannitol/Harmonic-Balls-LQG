import HarmonicBalls.Proofs.Sec6.FiniteWindowRootCollar
import HarmonicBalls.Proofs.Sec6.SingularRootCountTransfer

/-! # Nearby good-annulus counts on a finite window

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

open Classical in
/-- On a fixed finite family of scales, a deterministic displacement transfers
good-annulus counts from singular-mass sampled roots, up to a root count tail
and an explicitly controlled collar-frequency error. The displacement may
depend on the entire finite family and on the sampled-root law. -/
theorem exists_singularRoot_finiteWindow_goodAnnulus_count_le
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (s : Finset ℕ)
    {d q ε : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a a' amid b b' : ℝ) (m k : ℕ),
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) w a' b').card < m} ≤
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p |
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k} +
      (s.card : ℝ≥0∞) * q := by
  classical
  obtain ⟨η, hη, _, hcollar⟩ := exists_singularRoot_finite_relative_collar_failure_lt
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hac r hr s (show (0 : ℝ) < 1 by norm_num) hd hq
  obtain ⟨δ, hδ, ht⟩ := exists_singularRoot_goodAnnulus_count_probability_le
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hac hη hε
  refine ⟨δ, hδ, ?_⟩
  intro a a' amid b b' m k hb ha hslack
  have hsum : (∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ₀ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))}) ≤ (s.card : ℝ≥0∞) * q := by
    calc
      _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum (fun i hi => (hcollar i hi).le)
      _ = _ := by simp
  refine (ht r hr s a a' amid b b' d m k hb ha hslack).trans ?_
  gcongr

end HarmonicBalls.Section6
