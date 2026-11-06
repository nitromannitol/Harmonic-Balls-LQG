import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootNormalization
import HarmonicBalls.Proofs.Sec6.SingularMassRootCollar

/-! # Singular good-annulus counts for a finite window

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

open Classical in
/-- A weighted singular-mass root has a nearby-centre singular good-annulus
count bound on any prescribed finite family of scales. The displacement can
depend on the family, the root law, and the collar tolerance. -/
theorem exists_weighted_singularRoot_finiteWindow_count_le
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (ρ : ℝ) (x₀ : ℂ) (hρ : 0 < ρ)
    (v : ℂ → ℝ≥0∞) (hv : Measurable v)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (s : Finset ℕ)
    {c : ℝ} (hc : 0 < c) {d q ε : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q)
    (hε : 0 < ε) :
    let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
    ∃ η δ : ℝ, 0 < η ∧ η < c ∧ 0 < δ ∧
      ∀ (a a' amid b b' : ℝ) (m k : ℕ),
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
      (s.card : ℝ≥0∞) * q := by
  classical
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
  let : IsFiniteKernel κ := weightedRestrictionKernel_finite P μ _ _ _ _ _
  have hac := (weightedRestrictionKernel_middle_annulus P μ
    (h.aemeasurable_lqgMeasure hμ) x₀ ρ v hv).1
  obtain ⟨η, hη, hηc, hcollar⟩ :=
    exists_singularRoot_finite_singular_relative_collar_failure_lt
      hgrowth hγ hγ2 hα h hμ κ hac r hr s hc hd hq
  obtain ⟨δ, hδ, ht⟩ := exists_weighted_singularRoot_goodAnnulus_count_probability_le
    hgrowth hγ hγ2 hα h hμ hμ₀ ρ x₀ hρ v hv hη hε
  refine ⟨η, δ, hη, hηc, hδ, ?_⟩
  intro a a' amid b b' m k hb ha hslack hsep hsmall
  have hsum : (∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))}) ≤ (s.card : ℝ≥0∞) * q := by
    calc
      _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum (fun i hi => (hcollar i hi).le)
      _ = _ := by simp
  refine (ht r hr s a a' amid b b' d m k hb ha hslack hsep hsmall).trans ?_
  gcongr

end HarmonicBalls.Section6
