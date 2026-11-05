import HarmonicBalls.Draft.Section6
import HarmonicBalls.Draft.Section10

/-!
# A shared Harnack and crossing constant

The two frozen propositions have independently quantified witnesses. Decreasing
both to their positive minimum gives one witness, while retaining the events and
the universal prevalence constant of Proposition 6.2.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open Section6

universe u

/-- The component estimate persists when its mass threshold decreases. -/
theorem component_estimate_of_smaller_threshold
    {Ω : Type u} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (E : ℝ → ℂ → Set Ω) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤
          ENNReal.ofReal b * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅) :
    ∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
      ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
        μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤
          ENNReal.ofReal a * μ ω (annulus x₀ (ρ / 2) ρ) →
        Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  intro ω ρ hρ x₀ hω z hz t ht hball Λ hΛ hmass
  apply h ω ρ hρ x₀ hω z hz t ht hball Λ hΛ
  exact hmass.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hab) _)

/-- The crossing conclusion persists when its positive parameter decreases. -/
theorem crossing_bound_of_smaller_threshold
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ z : ℂ,
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ))
          w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / b⌉₊) :
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ z : ℂ,
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ))
          w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / a⌉₊ := by
  have hceil : (⌈1 / b⌉₊ : ℕ∞) ≤ ⌈1 / a⌉₊ := by
    exact_mod_cast Nat.ceil_mono (one_div_le_one_div_of_le ha hab)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, fun t ht z hz => (hρbound t ht z hz).trans hceil⟩

/-- The component/prevalence and crossing statements share one α.
Both hypotheses are conditional; this theorem does not prove either input. -/
theorem exists_shared_harnack_crossing_constant
    (hcomponent : HarnackTypeComponentStmt.{u})
    (hcrossing : ClusterBoundedCrossingsStmt.{u}) :
    ∃ c : ℝ, 0 < c ∧
    ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ α ∈ Ioo (0 : ℝ) 1, ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ α₀ hcirc μ →
    (∃ E : ℝ → ℂ → Set Ω,
      (∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ →
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closedBall x₀ ρ ⊆ ball 0 1 \ {z} →
        ∀ Λ ∈ connectedComponentsIn (cluster (μ ω) 1 z t ∩ ball x₀ ρ),
          μ ω (Λ ∩ annulus x₀ (ρ / 2) ρ) ≤
            ENNReal.ofReal α * μ ω (annulus x₀ (ρ / 2) ρ) →
          Λ ∩ closedBall x₀ (ρ / 2) = ∅) ∧
      PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
        c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
          ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧
            (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard : ℝ)}) ∧
    (∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ z : ℂ,
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ))
          w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊) := by
  obtain ⟨c, hc, hcomponent⟩ := hcomponent
  refine ⟨c, hc, fun γ hγ hγ2 => ?_⟩
  obtain ⟨a, ha, hcomponent⟩ := hcomponent γ hγ hγ2
  obtain ⟨b, hb, hcrossing⟩ := hcrossing γ hγ hγ2
  let α := min a (min b (1 / 2 : ℝ))
  have hαpos : 0 < α := lt_min ha (lt_min hb.1 (by norm_num))
  have hαa : α ≤ a := min_le_left _ _
  have hαb : α ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have hαone : α < 1 := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  refine ⟨α, ⟨hαpos, hαone⟩, fun α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  obtain ⟨E, hE, hprev⟩ := hcomponent α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  refine ⟨⟨E, component_estimate_of_smaller_threshold μ E hαa hE, hprev⟩, ?_⟩
  exact crossing_bound_of_smaller_threshold P μ hαpos hαb
    (hcrossing α₀ hα₀ Ω P hC hcirc μ hGFF hμ)

end HarmonicBalls
