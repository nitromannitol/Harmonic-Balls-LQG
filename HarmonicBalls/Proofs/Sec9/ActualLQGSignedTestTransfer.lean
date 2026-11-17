import HarmonicBalls.Proofs.Potential.LQGSingularGreenPotentialHolder
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-! # Signed Green potentials for the actual LQG measure

Bounded-domain Green potentials of finite compactly supported sources are
integrable and agree almost everywhere with their extended versions.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- On one event, finite compactly supported signed sources have integrable
Green potentials on every bounded observation set. Their real and extended
potentials agree almost everywhere, with a source-dependent exceptional set. -/
theorem IsWholePlaneGFF.ae_singular_signed_greenPotential_integrable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (O K₁ K₂ S : Set ℂ) (ν₁ ν₂ : Measure ℂ),
      IsOpen O → Bornology.IsBounded O → IsCompact K₁ → IsCompact K₂ →
      ν₁ K₁ᶜ = 0 → ν₂ K₂ᶜ = 0 → IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ →
      Bornology.IsBounded S →
      IntegrableOn (greenPotential O ν₁ - greenPotential O ν₂) S (μ ω) ∧
      (∀ᵐ x ∂(μ ω).restrict S,
        Integrable (greenFunction O x) ν₁ ∧ Integrable (greenFunction O x) ν₂ ∧
        ν₁ {x} = 0 ∧ ν₂ {x} = 0 ∧
        (∫⁻ y, greenKernelExtended O x y ∂ν₁) < ⊤ ∧
        (∫⁻ y, greenKernelExtended O x y ∂ν₂) < ⊤ ∧
        greenPotential O ν₁ x - greenPotential O ν₂ x =
          (∫⁻ y, greenKernelExtended O x y ∂ν₁).toReal -
            (∫⁻ y, greenKernelExtended O x y ∂ν₂).toReal) := by
  filter_upwards [hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hαQ hμ, hμ] with ω hb hlim
  let : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  have hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ ω (ball z r) ≤ ENNReal.ofReal (r ^ β) := by
    intro R _
    obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hb R
    obtain ⟨δ, hδ, hd⟩ := small_ball_power_absorb_constant hC hβ hr₀
      (fun z hz r hr hrr => (hb z hz r hr hrr).1)
    exact ⟨δ, β / 2, hδ, by positivity, hd⟩
  intro O K₁ K₂ S ν₁ ν₂ hO hOb hK₁ hK₂ hν₁ hν₂ hf₁ hf₂ hS
  let : IsFiniteMeasure ν₁ := hf₁
  let : IsFiniteMeasure ν₂ := hf₂
  have hi₁ := green_integrable_product_restrict_of_local_upper_growth hup hO hOb hK₁ hν₁ hS
  have hi₂ := green_integrable_product_restrict_of_local_upper_growth hup hO hOb hK₂ hν₂ hS
  refine ⟨?_, ?_⟩
  · exact hi₁.integral_prod_left.sub hi₂.integral_prod_left
  · obtain ⟨r, hr⟩ := hS.subset_ball (0 : ℂ)
    have ha₁ := Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hr le_rfl))
      (ae_greenPotential_of_local_upper_growth hup hO hOb hK₁ hν₁ r)
    have ha₂ := Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hr le_rfl))
      (ae_greenPotential_of_local_upper_growth hup hO hOb hK₂ hν₂ r)
    filter_upwards [ha₁, ha₂] with x h₁ h₂
    exact ⟨h₁.1, h₂.1, h₁.2.1, h₂.2.1, h₁.2.2.1, h₂.2.2.1,
      greenPotential_sub_eq_lintegral_toReal hOb h₁.2.1 h₂.2.1 h₁.1 h₂.1⟩

end HarmonicBalls
