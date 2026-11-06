import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootNormalization
import HarmonicBalls.Proofs.Sec6.SingularMassRootCollar
import HarmonicBalls.Proofs.Sec6.RescaledRootCollarFrequencyAC

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
count bound with one displacement valid for every finite scale family,
conditional on the stated sampled-root absolute continuity and reference-law
scaling. No independence between scales is assumed. -/
theorem exists_weighted_singularRoot_uniform_count_le_of_ac
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (ρ : ℝ) (x₀ : ℂ) (hρ : 0 < ρ)
    (v : ℂ → ℝ≥0∞) (hv : Measurable v)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (hνloc : ∀ ω, IsLocallyFiniteMeasure (ν ω))
    (Q₀ : Measure (Ω × ℂ)) [IsFiniteMeasure Q₀]
    (t : ℕ → Ω × ℂ → ℝ≥0∞) (ht : ∀ i, Measurable (t i))
    (ht0 : ∀ i p, t i p ≠ 0) (htop : ∀ i p, t i p ≠ ∞)
    (hscale : ∀ i,
      Q₀.map (fun p => t i p • ((ν p.1).map (fun x : ℂ => x-p.2)).map
        (fun x : ℂ => (r i)⁻¹ • x)) ≤
      Q₀.map (fun p => (ν p.1).map (fun x : ℂ => x-p.2)))
    (hreg : ∀ᵐ p ∂Q₀, ν p.1 (sphere p.2 3) = 0 ∧
      ν p.1 (sphere p.2 5) = 0 ∧ 0 < ν p.1 (annulus p.2 3 5))
    {c : ℝ} (hc : 0 < c) {d q ε : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q)
    (hε : 0 < ε) :
    let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
    (P ⊗ₘ κ) ≪ Q₀ →
    (∀ᵐ p ∂(P ⊗ₘ κ), μ p.1 = ν p.1) →
    ∃ η δ : ℝ, 0 < η ∧ η < c ∧ 0 < δ ∧
      ∀ (s : Finset ℕ) (a a' amid b b' : ℝ) (m k : ℕ),
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
  intro κ hac heq
  let : IsFiniteKernel κ := weightedRestrictionKernel_finite P μ _ _ _ _ _
  obtain ⟨η, hη, hηc, hcollar⟩ :=
    exists_rescaled_root_relativeCollar_failure_count_le_of_ac (P ⊗ₘ κ) Q₀
      ν hν hνloc r hr t ht ht0 htop hac hscale hreg hc hd hq
  obtain ⟨δ, hδ, ht⟩ := exists_weighted_singularRoot_goodAnnulus_count_probability_le
    hgrowth hγ hγ2 hα h hμ hμ₀ ρ x₀ hρ v hv hη hε
  refine ⟨η, δ, hη, hηc, hδ, ?_⟩
  intro s a a' amid b b' m k hb ha hslack hsep hsmall
  have hsum : (∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))}) ≤ (s.card : ℝ≥0∞) * q := by
    calc
      _ ≤ ∑ _i ∈ s, q := by
        apply Finset.sum_le_sum
        intro i hi
        have hevent : (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
            μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
              annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} =
          (P ⊗ₘ κ) {p | d * ν p.1 (annulus p.2 (3*r i) (5*r i)) <
            ν p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
              annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
          apply measure_congr
          filter_upwards [heq] with p hp
          simp only [hp]
        rw [hevent]
        simpa [Finset.filter_nonempty_iff] using hcollar {i} 1
      _ = _ := by simp
  refine (ht r hr s a a' amid b b' d m k hb ha hslack hsep hsmall).trans ?_
  gcongr

end HarmonicBalls.Section6
