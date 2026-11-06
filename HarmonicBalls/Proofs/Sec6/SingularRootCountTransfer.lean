import HarmonicBalls.Proofs.Sec6.RootedCollarCountTransfer

/-! # Good-annulus count transfer at singular-mass roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

open Classical in
/-- At singular-mass sampled roots, the probability of finding a nearby
centre with too few zero-singularity good annuli is controlled by the poor
count at the root and the collar-failure probabilities. The bound is uniform
in all nearby centres and requires no independence between scales. -/
theorem exists_singularRoot_goodAnnulus_count_probability_le
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ → ℝ), (∀ i, 0 < r i) →
      ∀ (s : Finset ℕ) (a a' amid b b' : ℝ) (d : ℝ≥0∞) (m k : ℕ),
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) w a' b').card < m} ≤
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p |
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k} +
      ∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ₀ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  classical
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_count_le hη hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr s a a' amid b b' d m k hbudget hmid hslack
  let Q := P ⊗ₘ κ
  let A : Set (Ω × ℂ) := {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
    (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) w a' b').card < m}
  let B : Set (Ω × ℂ) := {p |
    (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k}
  let C : Set (Ω × ℂ) := {p | k ≤ (s.filter fun i =>
    d * μ₀ p.1 (annulus p.2 (3*r i) (5*r i)) <
    μ₀ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
      annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card}
  have hmass := ae_singularRoot_zero_annulus_pos_finite hgrowth hγ hγ2 hα h hμ hμ₀ κ hac r hr
  have hsub : A ≤ᵐ[Q] B ∪ C := by
    filter_upwards [hmass] with p hp
    intro hA
    obtain ⟨w, hw, hwcount⟩ := hA
    have hc := ht (μ₀ p.1) r s p.2 w (fun i _ => hr i) hw a a' amid b b' d
      (fun i _ => (hp i).1) (fun i _ => (hp i).2) hbudget hmid hslack
    by_cases hb : (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m+k
    · exact Or.inl hb
    · right
      change k ≤ (s.filter fun i => d * μ₀ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ₀ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card
      omega
  have hbound : Q A ≤ Q B + Q C := (measure_mono_ae hsub).trans (measure_union_le B C)
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  have hc := mul_compProd_relativeCollarFailure_count_le P κ
    (h.aemeasurable_lqgMeasure hμ₀) (hV.mono fun _ hv => hv.1) r η d s k
  change (k : ℝ≥0∞) * Q C ≤ _ at hc
  calc
    _ = (k : ℝ≥0∞) * Q A := rfl
    _ ≤ (k : ℝ≥0∞) * (Q B + Q C) := by gcongr
    _ = (k : ℝ≥0∞) * Q B + (k : ℝ≥0∞) * Q C := mul_add _ _ _
    _ ≤ _ := by gcongr

end HarmonicBalls.Section6
