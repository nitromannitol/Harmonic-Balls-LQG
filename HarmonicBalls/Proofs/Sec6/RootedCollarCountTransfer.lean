import HarmonicBalls.Proofs.Sec6.CollarFailureFrequency
import HarmonicBalls.Proofs.Sec6.SingularRootRelativeCollar

/-! # Rooted collar counts and nearby-centre transfer

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

open Classical in
/-- The first-moment collar count estimate under a composition-product law,
for a random measure defined only almost everywhere. -/
theorem mul_compProd_relativeCollarFailure_count_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : Kernel Ω ℂ)
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (r : ℕ → ℝ) (η : ℝ) (d : ℝ≥0∞) (s : Finset ℕ) (k : ℕ) :
    (k : ℝ≥0∞) * (P ⊗ₘ κ) {p | k ≤ (s.filter fun i =>
      d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} ≤
    ∑ i ∈ s, (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  obtain ⟨ν, hν, hνloc, heq⟩ := exists_measurable_locallyFinite_rep hμ hloc
  have heq' := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp heq
  have hcount : (P ⊗ₘ κ) {p | k ≤ (s.filter fun i =>
      d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} =
    (P ⊗ₘ κ) {p | k ≤ (s.filter fun i =>
      d * ν p.1 (annulus p.2 (3*r i) (5*r i)) <
      ν p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} := by
    apply measure_congr
    filter_upwards [heq'] with p he
    change μ p.1 = ν p.1 at he
    simp only [he]
  have hevent (i : ℕ) : (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} =
    (P ⊗ₘ κ) {p | d * ν p.1 (annulus p.2 (3*r i) (5*r i)) <
      ν p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
    apply measure_congr
    filter_upwards [heq'] with p he
    change μ p.1 = ν p.1 at he
    simp only [he]
  rw [hcount]
  simp_rw [hevent]
  exact mul_measure_root_relativeCollarFailure_count_le (P ⊗ₘ κ) ν hν hνloc r η d s k

open Classical in
/-- A nearby centre can have too few good scales only if the sampled root
already has too few, or sufficiently many collar bounds fail. The estimate
holds simultaneously over all nearby centres, without requiring the event of
existence of such a centre to be measurable. -/
theorem exists_goodAnnulus_count_probability_le
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (Q : Measure (Ω × ℂ)) (μ : Ω → Measure ℂ)
      ( _hμ : Measurable μ) (_hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
      (r : ℕ → ℝ) (s : Finset ℕ), (∀ i ∈ s, 0 < r i) →
      ∀ (a a' amid b b' : ℝ) (d : ℝ≥0∞) (m k : ℕ),
      (∀ᵐ p ∂Q, ∀ i ∈ s, 0 < μ p.1 (annulus p.2 (3*r i) (5*r i)) ∧
        μ p.1 (annulus p.2 (3*r i) (5*r i)) ≠ ∞) →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      (k : ℝ≥0∞) * Q {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
        (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) w a' b').card < m} ≤
      (k : ℝ≥0∞) * Q {p |
        (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) p.2 a b).card < m + k} +
      ∑ i ∈ s, Q {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  classical
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_count_le hη hε
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ Q μ hμ hloc r s hr a a' amid b b' d m k hmass hbudget hmid hslack
  let A : Set (Ω × ℂ) := {p | ∃ w : ℂ, (∀ i ∈ s, dist w p.2 < δ * r i) ∧
    (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) w a' b').card < m}
  let B : Set (Ω × ℂ) := {p |
    (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) p.2 a b).card < m + k}
  let C : Set (Ω × ℂ) := {p | k ≤ (s.filter fun i =>
    d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
    μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
      annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card}
  have hsub : A ≤ᵐ[Q] B ∪ C := by
    filter_upwards [hmass] with p hp
    intro hA
    obtain ⟨w, hw, hwcount⟩ := hA
    have hc := ht (μ p.1) r s p.2 w hr hw a a' amid b b' d
      (fun i hi => (hp i hi).1) (fun i hi => (hp i hi).2) hbudget hmid hslack
    by_cases hb : (s.filter fun i => IsGoodAnnulus (μ p.1) (r i) p.2 a b).card < m+k
    · exact Or.inl hb
    · right
      change k ≤ (s.filter fun i => d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card
      omega
  have hbound : Q A ≤ Q B + Q C := (measure_mono_ae hsub).trans (measure_union_le B C)
  have hc := mul_measure_root_relativeCollarFailure_count_le Q μ hμ hloc r η d s k
  change (k : ℝ≥0∞) * Q C ≤ _ at hc
  calc
    _ = (k : ℝ≥0∞) * Q A := rfl
    _ ≤ (k : ℝ≥0∞) * (Q B + Q C) := by gcongr
    _ = (k : ℝ≥0∞) * Q B + (k : ℝ≥0∞) * Q C := mul_add _ _ _
    _ ≤ _ := by gcongr

universe u

/-- At singular-mass sampled roots, every annulus in a prescribed positive
countable family has positive finite zero-singularity mass. -/
theorem ae_singularRoot_zero_annulus_pos_finite
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∀ᵐ p ∂(P ⊗ₘ κ), ∀ n, 0 < μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) ∧
      μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) ≠ ∞ := by
  have hreg : ∀ᵐ p ∂(P ⊗ₘ κ), ∀ n,
      0 < μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_compProd_zero_annulus_regular_at_singular_roots
      hgrowth hγ hγ2 hα h hμ hμ₀ κ hac (hr n)] with p hp
    exact hp.2.2
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  have hloc : ∀ᵐ p ∂(P ⊗ₘ κ), IsLocallyFiniteMeasure (μ₀ p.1) :=
    (quasiMeasurePreserving_fst_compProd P κ).ae (hV.mono fun _ hv => hv.1)
  filter_upwards [hreg, hloc] with p hp hl n
  let : IsLocallyFiniteMeasure (μ₀ p.1) := hl
  exact ⟨hp n, ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)⟩

end HarmonicBalls.Section6
