import HarmonicBalls.Proofs.Sec6.WeightedSingularUniformCountLocalAC
import HarmonicBalls.Proofs.Sec6.WeightedRootAbsoluteContinuity

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
conditional on uniform absolute continuity of the rescaled unit-weight singular rooted laws restricted to a fixed ball. No independence between scales is assumed. -/
theorem exists_weighted_singularRoot_uniform_count_le_of_unit_local_uniform_ac
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
    (hνeq : ∀ᵐ ω ∂P, μ ω = ν ω)
    (t : ℕ → Ω × ℂ → ℝ≥0∞) (ht : ∀ i, Measurable (t i))
    (ht0 : ∀ i p, t i p ≠ 0) (htop : ∀ i p, t i p ≠ ∞)
    (hscale : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ (i : ℕ) (E : Set (Measure ℂ)), MeasurableSet E →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
        (fun _ => 1) measurable_const).map
          (fun p => ((ν p.1).map (fun x : ℂ => x-p.2)).restrict (ball 0 7)) E ≤ δ →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
        (fun _ => 1) measurable_const).map
          (fun p => (t i p • ((ν p.1).map (fun x : ℂ => x-p.2)).map
            (fun x : ℂ => (r i)⁻¹ • x)).restrict (ball 0 7)) E ≤ ε)
    {c : ℝ} (hc : 0 < c) {d q ε : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q)
    (hε : 0 < ε) :
    let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
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
  let κ₀ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall)
    (fun _ => 1) measurable_const
  let : IsFiniteKernel κ₀ := weightedRestrictionKernel_finite P μ _ _ _ _ _
  have hregμ := ae_compProd_singular_annulus_regular hgrowth hγ hγ2 hα h hμ κ₀
    ((weightedRestrictionKernel_middle_annulus P μ (h.aemeasurable_lqgMeasure hμ)
      x₀ ρ (fun _ => 1) measurable_const).1) (r := 1) (by norm_num)
  have hνeq₀ := (quasiMeasurePreserving_fst_compProd P κ₀).ae_eq_comp hνeq
  have hreg : ∀ᵐ p ∂(P ⊗ₘ κ₀), ν p.1 (sphere p.2 3) = 0 ∧
      ν p.1 (sphere p.2 5) = 0 ∧ 0 < ν p.1 (annulus p.2 3 5) := by
    filter_upwards [hregμ, hνeq₀] with p hp he
    change μ p.1 = ν p.1 at he
    simpa only [mul_one, he] using hp
  have hac := weighted_singular_middleAnnulus_root_ac_unit hgrowth hγ hγ2 hα h hμ
    x₀ hρ v hv
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (annulus x₀ (ρ/2) ρ) (measurableSet_ball.diff measurableSet_closedBall) v hv
  have hνeqw := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp hνeq
  exact exists_weighted_singularRoot_uniform_count_le_of_local_uniform_ac hgrowth hγ hγ2 hα h hμ hμ₀
    ρ x₀ hρ v hv r hr ν hν hνloc (P ⊗ₘ κ₀) t ht ht0 htop hscale hreg hc hd hq hε
    hac hνeqw

end HarmonicBalls.Section6
