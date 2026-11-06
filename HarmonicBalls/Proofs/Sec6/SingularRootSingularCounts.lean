import HarmonicBalls.Proofs.Sec6.SingularCollarGoodAnnulusCounts
import HarmonicBalls.Proofs.Sec6.RootedCollarCountTransfer

/-! # Singular good-annulus counts at sampled roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

open Classical in
/-- The finite count transfer at roots sampled from singular LQG mass. The
separation geometry and the singular collar marginal probabilities remain
explicit, and no independence between scales is assumed. -/
theorem exists_singularRoot_singular_goodAnnulus_count_probability_le
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
      ∀ (s : Finset ℕ) (ρ : ℝ) (x₀ : ℂ), 0 < ρ →
      ∀ (a a' amid b b' : ℝ) (d : ℝ≥0∞) (m k : ℕ),
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) *
        (ENNReal.ofReal (((401 : ℝ) ^ |-(γ * α)|) ^ 2) * d) ≤ ENNReal.ofReal amid →
      ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2*ρ)) →
      (∀ᵐ p ∂(P ⊗ₘ κ),
        (∀ i ∈ s, annulus p.2 (3*r i) (5*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) ∧
        (∀ i ∈ s, annulus p.2 (3*r i-η*r i) (5*r i+η*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) ∧
        (∀ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) → ∀ i ∈ s,
          r i / 100 ≤ infDist (0 : ℂ) (annulus w (3*r i) (5*r i)))) →
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
        (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) w
          (a' / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b').card < m} ≤
      (k : ℝ≥0∞) * (P ⊗ₘ κ) {p |
        (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k} +
      ∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  classical
  obtain ⟨δ, hδ, ht⟩ := exists_singular_goodAnnulus_count_le hη hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr s ρ x₀ hρ a a' amid b b' d m k hbudget hmid hslack hdist hgeom
  let Q := P ⊗ₘ κ
  let A : Set (Ω × ℂ) := {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
    (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) w
      (a' / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) b').card < m}
  let B : Set (Ω × ℂ) := {p |
    (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m + k}
  let C : Set (Ω × ℂ) := {p | k ≤ (s.filter fun i =>
    d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
    μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
      annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card}
  have hmass := ae_singularRoot_zero_annulus_pos_finite hgrowth hγ hγ2 hα h hμ hμ₀ κ hac r hr
  have hweight := (quasiMeasurePreserving_fst_compProd P κ).ae
    (ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀)
  have hsub : A ≤ᵐ[Q] B ∪ C := by
    filter_upwards [hmass, hweight, hgeom] with p hp he hg
    intro hA
    obtain ⟨w, hw, hwcount⟩ := hA
    have hwgt : (μ p.1).restrict {0}ᶜ = ((μ₀ p.1).withDensity
        fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))).restrict {0}ᶜ := by rw [he]
    have hc := ht (μ p.1) (μ₀ p.1) r s ρ (-(γ * α)) p.2 w x₀ hρ
      (fun i _ => hr i) hw a a' amid b b' d
      (fun i _ => (hp i).1) (fun i _ => (hp i).2) hbudget hmid hslack
      hdist hwgt hg.1 hg.2.1 (hg.2.2 w hw)
    by_cases hb : (s.filter fun i => IsGoodAnnulus (μ₀ p.1) (r i) p.2 a b).card < m+k
    · exact Or.inl hb
    · right
      change k ≤ (s.filter fun i => d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card
      omega
  have hbound : Q A ≤ Q B + Q C := (measure_mono_ae hsub).trans (measure_union_le B C)
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  have hc := mul_compProd_relativeCollarFailure_count_le P κ
    (h.aemeasurable_lqgMeasure hμ) (hV.mono fun _ hv => hv.1) r η d s k
  change (k : ℝ≥0∞) * Q C ≤ _ at hc
  calc
    _ = (k : ℝ≥0∞) * Q A := rfl
    _ ≤ (k : ℝ≥0∞) * (Q B + Q C) := by gcongr
    _ = (k : ℝ≥0∞) * Q B + (k : ℝ≥0∞) * Q C := mul_add _ _ _
    _ ≤ _ := by gcongr

end HarmonicBalls.Section6
